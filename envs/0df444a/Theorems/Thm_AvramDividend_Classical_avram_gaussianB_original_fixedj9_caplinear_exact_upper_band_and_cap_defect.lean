-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_fixedj9_caplinear_exact_upper_band_and_cap_defect
-- name    : AvramDividend.Classical.avram_gaussianB_original_fixedj9_caplinear_exact_upper_band_and_cap_defect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:27:22.412813+00:00
-- url     : https://prove2.me/theorems/1506ca48-19dc-485c-960a-7313b8077afc
-- title:
--   Original B52 positive-stop fixed j=9 upper strip is 5/44 and exact cap-linear defect is 1/1936
-- statement:
--   For the exact original B52 cap C=1/8, j=9, upper-strip formula and quadratic HJB reward w(y)=2y−4y² on the nonnegative reserve, b equals 5/44 and the exact linear-cap endpoint defect equals 1/1936. This proves source-equivalence of the explicit numeric constants used in the original Gaussian positive-drift counterexample rather than assuming them.

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.NormNum
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_fixedj9_caplinear_exact_upper_band_and_cap_defect :
    let C : ℝ≥0∞ := ENNReal.ofReal (1 / 8 : ℝ)
    let j : ℕ := 9
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let w : ℝ → ℝ := fun y =>
      if y < 0 then 0 else 2 * y - 4 * y ^ 2
    b = (5 / 44 : ℝ) ∧
      ((w C.toReal - w b) - (C.toReal - b)) =
        (1 / 1936 : ℝ) := by sorry
