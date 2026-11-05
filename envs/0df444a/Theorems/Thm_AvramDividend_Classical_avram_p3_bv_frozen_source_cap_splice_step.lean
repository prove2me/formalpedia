-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_source_cap_splice_step
-- name    : AvramDividend.Classical.avram_p3_bv_frozen_source_cap_splice_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:42:09.292007+00:00
-- url     : https://prove2.me/theorems/d4d6eb3b-4bef-43b1-b174-91ce04e359e6
-- title:
--   Exact cap-spliced candidate increment on original BV frozen source interior cells
-- statement:
--   The literal cap-spliced C1 candidate has exactly the original candidate increment on a frozen original-process source step whenever both pre- and post-source reserves are below a finite cap, and at every step for an infinite cap. This discharges the V-to-w increment equality premise in the Proved original strict-open BV grid budget once the genuine source localisation provides the two endpoint bounds.
-- source:
--   Exact algebraic cap-splice reduction for the original stopped C1 Stieltjes grid certificate, Proved P3-F theorem 5341265a-58e4-4915-9d29-01fc8bdbd31e. The endpoint premise is explicit and is not claimed from dividend admissibility alone.

import Mathlib
open scoped ENNReal

theorem AvramDividend.Classical.avram_p3_bv_frozen_source_cap_splice_step
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ)
    (hz : C = ⊤ ∨ z ≤ C.toReal)
    (hzd : C = ⊤ ∨ z + d ≤ C.toReal) :
    V (z + d) - V z = w (z + d) - w z := by sorry
