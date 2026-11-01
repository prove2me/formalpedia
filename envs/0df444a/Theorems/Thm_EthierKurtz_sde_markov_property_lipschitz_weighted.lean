-- Prove2me | Theorems.Thm_EthierKurtz_sde_markov_property_lipschitz_weighted
-- name    : EthierKurtz.sde_markov_property_lipschitz_weighted
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-01T00:47:33.896342+00:00
-- url     : https://prove2.me/theorems/70fef014-c635-47fc-8863-c09240ca519f
-- title:
--   Markov property of SDE solutions with locally Lipschitz coefficients, conditional form with a bounded weight measurable for the Brownian past
-- statement:
--   Let $X^y$ ($y\in D$) solve $dX=\sigma_0(X)\,dW+b_0(X)\,dt$, $X_0=y$, with continuous $\sigma_0,b_0$ that agree on $\bar B_{R+3}$ with globally bounded, globally Lipschitz $s_1^R,b_1^R$ for every $R\in\mathbb N$. For every $t\ge0$ and every measurable $f$ with $|f|\le K$ and $|f(x)-f(x')|\le L_f|x-x'|$ there is a measurable $g$, $|g|\le K$, with $g(y)=\mathbb E f(X^y_t)$ for $y\in D$ and, for every $x\in D$, $s>0$ with $X^x_s\in D$ a.s. and every weight $Z$ with $|Z|\le1$ that is measurable for the completed Brownian past $\mathcal F_s$,
--
--   $$\mathbb E\big[Z\, f(X^x_{s+t})\big]=\mathbb E\big[Z\, g(X^x_s)\big],$$
--
--   that is, $\mathbb E[f(X^x_{s+t})\mid\mathcal F_s]=g(X^x_s)$.
--
--   Role: the conditional Markov property of the stochastic Kolmogorov system, used in the proof of (4.18) of Theorem 4.1 to restart the process at the random times of a Feynman-Kac clock.
--
--   **Formalization Note**: the conditional expectation is stated in weak form, tested against every bounded $\mathcal F_s$-measurable weight `Zw`.
-- source:
--   X. Mao, Stochastic Differential Equations and Applications, 2nd ed., Horwood 2007, https://doi.org/10.1533/9780857099402, Theorem 2.9.3 (Markov property of solutions); I. Karatzas, S. E. Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer 1991, https://doi.org/10.1007/978-1-4612-0949-2, Theorem 5.4.20 (strong Markov property for SDE solutions)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem sde_markov_property_lipschitz_weighted {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (s₁ : ℕ → SDEState d → SDEDiffusion d) (b₁ : ℕ → SDEState d → SDEState d) (S L : ℕ → ℝ)
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL : ∀ R, 0 ≤ L R)
    (hSg : ∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R)
    (hLg : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖)
    (hag : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {D : Set (SDEState d)} {X : SDEState d → ℝ≥0 → Ω → SDEState d}
    (hX : ∀ y ∈ D, SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) (X y))
    (t : ℝ≥0) {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K)
    (hLf : 0 ≤ Lf) (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) :
    ∃ g : SDEState d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ K) ∧
      (∀ y ∈ D, g y = ∫ ω, f (X y t ω) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, 0 < s → (∀ᵐ ω ∂P, X x s ω ∈ D) → ∀ Zw : Ω → ℝ,
        Measurable[completedBrownianPast P W (fun _ => x) s] Zw → Measurable Zw →
        (∀ ω, |Zw ω| ≤ 1) →
        ∫ ω, Zw ω * f (X x (s + t) ω) ∂P = ∫ ω, Zw ω * g (X x s ω) ∂P := by sorry

end EthierKurtz
