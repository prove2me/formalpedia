-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
-- name    : AvramDividend.Classical.avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:25:23.717974+00:00
-- url     : https://prove2.me/theorems/85617d04-b6a9-454d-85db-1e19a7a69c1b
-- title:
--   Cap-linear extension equals original supersolution on the full closed capped interval
-- statement:
--   For any positive finite or infinite ENNReal cap and all reserve states in the closed capped interval, the cap-linear extension V is exactly the original candidate w. The endpoint cases z=0 and z=C are included, and the C=⊤ branch is explicit.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- The cap-linear value extension agrees with the candidate at every closed-cap postpayment state, including zero and the cap. -/
--   theorem solution
--       (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
--       (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
--       (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
--         V z = if z ≤ C.toReal then w z
--           else w C.toReal + (z - C.toReal))
--       (z : ℝ) (hz0 : 0 ≤ z) (hzC : ENNReal.ofReal z ≤ C) :
--       V z = w z := by
--     by_cases htop : C = ⊤
--     · exact hVtop htop z
--     · have hReal : z ≤ C.toReal := by
--         have h := ENNReal.toReal_mono htop hzC
--         rw [ENNReal.toReal_ofReal hz0] at h
--         exact h
--       rw [hVfinite htop z]
--       exact if_pos hReal

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z : ℝ) (hz0 : 0 ≤ z) (hzC : ENNReal.ofReal z ≤ C) :
    V z = w z := by sorry
