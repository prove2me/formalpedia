-- Prove2me | Theorems.Thm_Avram2004_Canadized_corollary1_value_at_tau
-- name    : Avram2004.Canadized.corollary1_value_at_tau
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T06:50:15.63815+00:00
-- url     : https://prove2.me/theorems/fc7e6c2e-364c-4ec6-90d9-d97d899b8970
-- title:
--   Corollary 1, Eq. (29) — the value of stopping the reflected process at τ_k under ℙ¹
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $a>0$ and $q=a+r$. For $k\ge0$ let $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$, where under $\mathbb P^1_{-z}$ the reflected process $Y=\overline X-X$ starts at $Y_0=z\ge0$. Then
--   $$
--   \mathbb E^1_{-z}\big(e^{-a\tau_k+Y_{\tau_k}}\big)=e^z\left(Z^{(q)}(k-z)+\frac{Z^{(q)}(k)-qW^{(q)}(k)}{W^{(q)\prime}(k)-W^{(q)}(k)}\,W^{(q)}(k-z)\right),
--   $$
--   where $W^{(q)}$ and $Z^{(q)}$ are the scale functions of $(X,\mathbb P)$ (not of $(X,\mathbb P^1)$).
--
--   This is the value of the threshold strategy "exercise when $Y$ first reaches level $k$". In the Canadized problem it is applied with $a=\alpha+\lambda$, so that $q=p$, to compute the value of $\tau_k\wedge\eta(\lambda)$ in Lemma 3.
--
--   **Formalization Note** The paper's parameter $\alpha$ is renamed $a$, since §7 uses the corollary at $a=\alpha+\lambda$. The expectation is a lower Lebesgue integral in $[0,\infty]$ with payoff $0$ on $\{\tau_k=\infty\}$; the equality with the real right-hand side also asserts that the expectation is finite. $W^{(q)\prime}(k)$ is the derivative of $W^{(q)}$ at $k$; its existence on $(0,\infty)$ is a consequence of the standing assumption, not an added hypothesis. For $k=0$, $\tau_0=0$ and both sides equal $e^z$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 228, Corollary 1, Eq. (29)

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- Corollary 1, (29), p. 228: with `ψ(1) = r ≥ 0`, `Q = ℙ^1` the Esscher measure, `a > 0` and `q = a + r`,
for `k ≥ 0` and `z ≥ 0`, under `ℙ^1_{-z}` (`Y = refl 0 (-z) X`),
`𝔼^1_{-z}(e^{-aτ_k + Y_{τ_k}}) = e^z (Z^{(q)}(k - z) + (Z^{(q)}(k) - qW^{(q)}(k)) / (W^{(q)′}(k) - W^{(q)}(k)) W^{(q)}(k - z))`,
with the scale functions of `(X, P)`. (The paper's `α` is renamed `a`: §7 uses it at `a = α + λ`.) -/
theorem corollary1_value_at_tau {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (a q : ℝ) (ha : 0 < a) (hq : q = a + r)
    (k z : ℝ) (hk : 0 ≤ k) (hz : 0 ≤ z) :
    ∫⁻ ω, payoffAt a (Shared.refl 0 (-z) X) (Shared.tau 0 (-z) X k) ω ∂Q =
      ENNReal.ofReal (Real.exp z *
        (Shared.Z P X 0 q (k - z)
          + (Shared.Z P X 0 q k - q * Shared.W P X 0 q k) / (deriv (Shared.W P X 0 q) k - Shared.W P X 0 q k)
            * Shared.W P X 0 q (k - z))) := by sorry

end Avram2004.Canadized
