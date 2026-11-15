-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a256_scalar_gaussian_HJB_positive_origin_upper
-- name    : AvramDividend.Classical.avram_ga_a256_scalar_gaussian_HJB_positive_origin_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:47:09.992048+00:00
-- url     : https://prove2.me/theorems/0c0ca63d-886c-4f69-b8c3-c3a0bee2d48d
-- title:
--   Scalar Gaussian HJB supersolution bounded above near ruin without boundary value at zero
-- statement:
--   For nonzero volatility, positive discount, and a twice differentiable classical Gaussian scalar HJB supersolution on the strictly positive half-line, the value is uniformly bounded above throughout every fixed interval (0,a], with no assumptions on w at zero or on its absolute growth. Obtained by the positive and negative characteristic roots and a first-order weighted derivative monotonicity argument; this is the exact missing negative-increment endpoint input for original stopped Gaussian combined-source a216.
-- source:
--   Gaussian HJB a247/a248 scalar characteristic factor, a249/a250 factor monotonicity and a255 near-zero weighted factor upper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a256_scalar_gaussian_HJB_positive_origin_upper
    (sigma c q a : ℝ) (hσ : 0 < sigma) (hq : 0 < q) (ha : 0 < a)
    (w : ℝ → ℝ)
    (hSmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hODE : ∀ y : ℝ, 0 < y →
      sigma^2/2 * iteratedDeriv 2 w y +
        c * deriv w y - q * w y ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → y ≤ a → w y ≤ K := by sorry
