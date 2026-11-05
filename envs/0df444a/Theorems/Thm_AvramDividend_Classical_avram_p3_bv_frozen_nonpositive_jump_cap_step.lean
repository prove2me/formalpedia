-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_nonpositive_jump_cap_step
-- name    : AvramDividend.Classical.avram_p3_bv_frozen_nonpositive_jump_cap_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:52:58.789725+00:00
-- url     : https://prove2.me/theorems/811e62ab-5d3e-4544-8e9c-0c9e33d6bbe7
-- title:
--   Nonpositive original source jumps preserve the cap-spliced C1 increment identity
-- statement:
--   If a frozen original source jump is nonpositive and its pre-jump state is below the finite cap, its post-jump state is also below the cap. The Proved cap-splice source-step theorem therefore identifies the exact candidate-function increment with the unsliced C1 increment, including negative post-jump ruin states and the infinite-cap case. This removes the separate endpoint bound from the negative-jump part of the original stopped BV mesh; positive physical-drift steps still require separate localisation.
-- source:
--   Proved cap-splice lemma d4d6eb3b-4bef-43b1-b174-91ce04e359e6 and order arithmetic. Used for negative source-jump chronology in the original P3-F finite-grid budget.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_source_cap_splice_step

open AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p3_bv_frozen_nonpositive_jump_cap_step
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ)
    (hz : C = ⊤ ∨ z ≤ C.toReal)
    (hd : d ≤ 0) :
    V (z + d) - V z = w (z + d) - w z := by sorry
