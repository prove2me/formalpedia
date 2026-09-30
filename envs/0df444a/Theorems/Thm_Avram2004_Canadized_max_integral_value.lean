-- Prove2me | Theorems.Thm_Avram2004_Canadized_max_integral_value
-- name    : Avram2004.Canadized.max_integral_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:17:10.224983+00:00
-- url     : https://prove2.me/theorems/8136d489-0df3-4d08-b1ef-dfb7c81646fb
-- title:
--   §7, proof of Lemma 3 — the expected discounted dX̄ integral up to τ_k
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. Under $\mathbb P^1_{s,x}$ with $s-x\ge0$, let $\overline X$ be the running maximum, $Y=\overline X-X$ the reflected process and, for $k>0$, $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$. Then
--   $$
--   \mathbb E^1_{s,x}\Big[\int_0^{\tau_k}e^{-(\alpha+\lambda)t+Y_t}\,d\overline X_t\Big]=e^{s-x}\,\frac{W^{(p)}(k-s+x)}{W^{(p)\prime}(k)-W^{(p)}(k)},
--   $$
--   where $W^{(p)}$ is the $p$-scale function of $(X,\mathbb P)$.
--
--   Together with the Itô identity (34) and Corollary 1 (at discount rate $\alpha+\lambda$) this yields the value of the threshold rule in Lemma 3.
--
--   **Formalization Note** The left side is a lower Lebesgue integral of a pathwise Lebesgue–Stieltjes integral, in $[0,\infty]$; the equality with the real right-hand side also asserts finiteness. $W^{(p)\prime}(k)$ is the derivative at $k>0$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 233, proof of Lemma 3, display before the end of the proof

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

/-- §7, proof of Lemma 3, p. 233 (display before the end of the proof): for `k > 0` and `s - x ≥ 0`,
under `ℙ^1_{s,x}` (`Y = refl s x X`), with `p = α + λ + r` and the scale functions of `(X, P)`,
`𝔼^1_{s,x}[∫_0^{τ_k} e^{-(α+λ)t+Y_t} dX̄_t] = e^{s-x} W^{(p)}(k - s + x) / (W^{(p)′}(k) - W^{(p)}(k))`. -/
theorem max_integral_value {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (s x k : ℝ) (hsx : x ≤ s) (hk : 0 < k) :
    ∫⁻ ω, maxIntegral (α + lam) s x X (Shared.tau s x X k) ω ∂Q =
      ENNReal.ofReal (Real.exp (s - x) * Shared.W P X 0 p (k - s + x)
        / (deriv (Shared.W P X 0 p) k - Shared.W P X 0 p k)) := by sorry

end Avram2004.Canadized
