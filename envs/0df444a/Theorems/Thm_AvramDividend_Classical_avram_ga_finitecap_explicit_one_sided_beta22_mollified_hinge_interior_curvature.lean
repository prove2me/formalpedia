-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_finitecap_explicit_one_sided_beta22_mollified_hinge_interior_curvature
-- name    : AvramDividend.Classical.avram_ga_finitecap_explicit_one_sided_beta22_mollified_hinge_interior_curvature
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:56:04.453504+00:00
-- url     : https://prove2.me/theorems/804d9484-9e33-4d55-a0de-37db0ddc06d2
-- title:
--   Exact nonnegative Gaussian curvature of the one-sided Beta(2,2) mollified cap kink inside its smoothing strip
-- statement:
--   For the explicit one-sided Beta(2,2) kernel 6z(1-z) supported on the unit interval, the mollification of the positive hinge (y-b)^+ at bandwidth epsilon is zero below b, equals (y-b)^3/epsilon^2-(y-b)^4/(2epsilon^3) on (b,b+epsilon), and equals y-b-epsilon/2 above b+epsilon. Prove the exact first and second classical derivatives and nonnegative second derivative at every y strictly inside (b,b+epsilon). Multiplying by the negative original cap kink amplitude 1-w'(b) gives the correct nonpositive Gaussian smoothing contribution. This verifies the interior source of the weak kink term without assuming second-derivative interchange through a discontinuity.
-- source:
--   Original finitecap stopped Ito-Stieltjes source 0ef5d778 requires nonpositive cap-kink Gaussian smoothing correction. This explicit regularisation is the first concrete analytic lemma towards proving rather than assuming the weak derivative identity hWeak in already Proved 1d8fa7f6.

import Mathlib
open Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_finitecap_explicit_one_sided_beta22_mollified_hinge_interior_curvature
    (b ε y : ℝ) (hε : 0 < ε) (hy : b < y) (hu : y < b + ε) :
    let Q : ℝ → ℝ := fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
          (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
        else z - b - ε / 2
    deriv Q y = (3 / ε ^ 2) * (y - b) ^ 2 - (2 / ε ^ 3) * (y - b) ^ 3 ∧
    iteratedDeriv 2 Q y = (6 / ε ^ 2) * (y - b) - (6 / ε ^ 3) * (y - b) ^ 2 ∧
    0 ≤ iteratedDeriv 2 Q y := by sorry
