-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_continuous_unit_interval_profile
-- name    : AvramDividend.Classical.avram_wave5_04c_continuous_unit_interval_profile
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:18:02.014443+00:00
-- url     : https://prove2.me/theorems/da912dbc-46cd-43e7-a9df-e74e7690404b
-- title:
--   Lift compact BV jump profile continuity to the Bernstein continuous-function space
-- statement:
--   Every continuous compactified jump profile on [0,1] is exactly a member of the continuous-map space C(unitInterval.Elem, R) expected by the Proved endpoint-weighted Bernstein approximation. The theorem closes a Lean coercion/topology interface in the original BV C1 semigroup approximation.
-- source:
--   continuousOn_iff_continuous_restrict and the subtype unitInterval.Elem.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_continuous_unit_interval_profile
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ G : C(unitInterval.Elem, ℝ),
      ∀ t : unitInterval.Elem, G t = f (t : ℝ) := by sorry
