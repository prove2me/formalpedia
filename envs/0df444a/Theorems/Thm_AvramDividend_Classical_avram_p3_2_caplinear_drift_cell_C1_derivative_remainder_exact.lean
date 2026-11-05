-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_caplinear_drift_cell_C1_derivative_remainder_exact
-- name    : AvramDividend.Classical.avram_p3_2_caplinear_drift_cell_C1_derivative_remainder_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:46:53.529198+00:00
-- url     : https://prove2.me/theorems/8f436476-c1cd-449f-930c-8e84381fa3ee
-- title:
--   Original capped BV drift cell exactly equals C1 generator drift plus Taylor remainder
-- statement:
--   For the actual original cap-linear envelope V, on any physical BV drift cell whose post-rightpayment reserve z and pure drift-upshift z+c remain in the closed cap, the V drift increment is exactly deriv w z*c plus its explicit first-order w C1 Taylor remainder. The identity holds at cap contact and for C=top; no assumption about drift sign or equality-in-law. This is the exact generator-form conversion needed by the accepted source-original physical Stieltjes cash budget 7266a3c5 and new pure-drift Taylor mesh convergence.
-- source:
--   Original V cap-linear definition and source-exact capped-reserve drift-upshift conditions; elementary ring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_caplinear_drift_cell_C1_derivative_remainder_exact
    (w : ℝ → ℝ) (C : ℝ≥0∞) (z c : ℝ)
    (hCap : C = ⊤ ∨ z ≤ C.toReal)
    (hUp : C = ⊤ ∨ z + c ≤ C.toReal) :
    let V : ℝ → ℝ := fun y =>
      if C = ⊤ then w y
      else if y ≤ C.toReal then w y
      else w C.toReal + (y - C.toReal)
    V (z + c) - V z =
      deriv w z * c +
      (w (z + c) - w z - deriv w z * c) := by sorry
