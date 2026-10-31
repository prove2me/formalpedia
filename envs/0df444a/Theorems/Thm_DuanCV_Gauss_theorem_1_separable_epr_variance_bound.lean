-- Prove2me | Theorems.Thm_DuanCV_Gauss_theorem_1_separable_epr_variance_bound
-- name    : DuanCV.Gauss.theorem_1_separable_epr_variance_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:31.896001+00:00
-- url     : https://prove2.me/theorems/367dfa80-9c4e-4428-88e2-4d34438be80f
-- title:
--   Theorem 1 — every separable state satisfies $\langle(\Delta\hat u)^2\rangle+\langle(\Delta\hat v)^2\rangle\ge a^2+1/a^2$
-- statement:
--   Let $\rho$ be a separable state of two modes, Gaussian or not, and let $a\neq0$ be real. For the EPR-like operators
--
--   $$\hat u=|a|\hat x_1+\frac1a\hat x_2,\qquad \hat v=|a|\hat p_1-\frac1a\hat p_2,$$
--
--   with $[\hat x_j,\hat p_{j'}]=i\delta_{jj'}$, the total variance satisfies
--
--   $$\bigl\langle(\Delta\hat u)^2\bigr\rangle_\rho+\bigl\langle(\Delta\hat v)^2\bigr\rangle_\rho\ \ge\ a^2+\frac1{a^2}.$$
--
--   A violation of this bound therefore certifies entanglement of an arbitrary continuous variable state. This is the 'only if' half of the criterion of Theorem 2.
--
--   Differences from the source:
--   - reading: Eq. (1): ρ = ∑ᵢ pᵢ ρᵢ₁ ⊗ ρᵢ₂ with the index range left open → ρ lies in the trace-norm closed convex hull of product states (Holevo–Shirokov–Werner); reason: the paper's own proof of Theorem 2 concludes separability from the continuous mixture (19), and the closed hull contains every finite, countable and integral mixture of product states
--   - encoding: ⟨(Δû)²⟩_ρ for a quadrature û = w·r̂ → the variance in ℝ≥0∞ of the unique probability law on ℝ whose characteristic function is the Weyl trace tr ρ exp(i t w·r̂); reason: this is the variance of the observable; the value is ⊤ when the second moment is infinite, a case the paper does not discuss and in which (3) holds trivially
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Theorem 1, Eqs. (2)–(3), pp. 1–2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_DuanCV_Gauss_IsSeparableTwoMode
import Definitions.Def_DuanCV_Gauss_quadVariance
import Definitions.Def_DuanCV_Gauss_eprU
import Definitions.Def_DuanCV_Gauss_eprV

open QAlgorithms.Papers.Independent.Claimed50.P19 (FockIndex)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

namespace DuanCV.Gauss

/-- **Theorem 1 (sufficient criterion for inseparability).**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Theorem 1, pp. 1–2, Eqs. (2)–(3).

For every separable state `ρ` of two modes, Gaussian or not, and every real `a ≠ 0`, the operators
`û = |a|x̂₁ + (1/a)x̂₂`, `v̂ = |a|p̂₁ - (1/a)p̂₂` satisfy
`⟨(Δû)²⟩_ρ + ⟨(Δv̂)²⟩_ρ ≥ a² + 1/a²`.

**Formalization Note.** Variances live in `ℝ≥0∞`: a state with infinite variance satisfies the bound.
Separable means the closed convex hull of product states. -/
theorem theorem_1_separable_epr_variance_bound (ρ : State (FockIndex 2))
    (hρ : IsSeparableTwoMode ρ.coefficients) (a : ℝ) (ha : a ≠ 0) :
    ENNReal.ofReal (a ^ 2 + 1 / a ^ 2) ≤
      quadVariance ρ.coefficients (eprU a 1) + quadVariance ρ.coefficients (eprV a (-1)) := by sorry

end DuanCV.Gauss
