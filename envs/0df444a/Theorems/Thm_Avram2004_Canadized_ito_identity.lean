-- Prove2me | Theorems.Thm_Avram2004_Canadized_ito_identity
-- name    : Avram2004.Canadized.ito_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:08:36.505979+00:00
-- url     : https://prove2.me/theorems/c8cb4fbc-2678-4b1b-888c-b237c22c8fed
-- title:
--   Eq. (34) — Itô identity for e^{−(α+λ)t+Y_t} up to τ_k under ℙ¹_{s,x}
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. Consider the process with starting position $x$ and prior maximum $s$, $s-x\ge0$ (the paper's $\mathbb P^1_{s,x}$), its running maximum $\overline X$ and reflected process $Y=\overline X-X$, $Y_0=s-x$. For $k>0$ let $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$. Then the three expectations below are finite and
--   $$
--   p\,\mathbb E^1_{s,x}\Big[\int_0^{\tau_k}e^{-(\alpha+\lambda)t+Y_t}\,dt\Big]=e^{s-x}-\mathbb E^1_{s,x}\big[e^{-(\alpha+\lambda)\tau_k+Y_{\tau_k}}\big]+\mathbb E^1_{s,x}\Big[\int_0^{\tau_k}e^{-(\alpha+\lambda)t+Y_t}\,d\overline X_t\Big].
--   $$
--   The last integral is the pathwise Lebesgue–Stieltjes integral against the nondecreasing path $t\mapsto\overline X_t$.
--
--   This identity reduces the running reward of the Canadized problem, evaluated at the threshold time $\tau_k$, to the terminal payoff (given by Corollary 1) and to an integral against the running maximum (computed in the proof of Lemma 3).
--
--   **Formalization Note** All three expectations are lower Lebesgue integrals in $[0,\infty]$; the conclusion asserts that each is finite and states the identity in the rearranged form $p\cdot A+B=e^{s-x}+C$, which avoids subtraction in $[0,\infty]$ and, given finiteness, is equivalent to the page's display. The payoff at $\tau_k$ is $0$ on $\{\tau_k=\infty\}$ and the integrals run over $(0,\infty)$ there.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 232, proof of Lemma 3, Eq. (34)

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem
import Definitions.Def_Avram2004_Canadized_maxIntegral

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- (34), p. 232: for `k > 0` and a starting state with `s - x ≥ 0`, under `ℙ^1_{s,x}` (`Y = refl s x X`,
`Y_0 = s - x`), with `p = α + λ + r`, the three expectations
`A = 𝔼^1_{s,x}[∫_0^{τ_k} e^{-(α+λ)t+Y_t} dt]`, `B = 𝔼^1_{s,x}[e^{-(α+λ)τ_k+Y_{τ_k}}]` and
`C = 𝔼^1_{s,x}[∫_0^{τ_k} e^{-(α+λ)t+Y_t} dX̄_t]` (the last a pathwise Lebesgue–Stieltjes integral against the
running maximum) are finite and `p A = e^{s-x} - B + C`, stated as `p A + B = e^{s-x} + C` in `[0, ∞]`. -/
theorem ito_identity {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (s x k : ℝ) (hsx : x ≤ s) (hk : 0 < k) :
    (∫⁻ ω, runIntegral (α + lam) (Shared.refl s x X) (Shared.tau s x X k) ω ∂Q) < ⊤ ∧
      (∫⁻ ω, payoffAt (α + lam) (Shared.refl s x X) (Shared.tau s x X k) ω ∂Q) < ⊤ ∧
      (∫⁻ ω, maxIntegral (α + lam) s x X (Shared.tau s x X k) ω ∂Q) < ⊤ ∧
      ENNReal.ofReal p * (∫⁻ ω, runIntegral (α + lam) (Shared.refl s x X) (Shared.tau s x X k) ω ∂Q)
          + ∫⁻ ω, payoffAt (α + lam) (Shared.refl s x X) (Shared.tau s x X k) ω ∂Q =
        ENNReal.ofReal (Real.exp (s - x))
          + ∫⁻ ω, maxIntegral (α + lam) s x X (Shared.tau s x X k) ω ∂Q := by sorry

end Avram2004.Canadized
