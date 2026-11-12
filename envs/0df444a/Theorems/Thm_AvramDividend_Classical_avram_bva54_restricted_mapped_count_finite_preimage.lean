-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva54_restricted_mapped_count_finite_preimage
-- name    : AvramDividend.Classical.avram_bva54_restricted_mapped_count_finite_preimage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:38:17.041862+00:00
-- url     : https://prove2.me/theorems/044955c9-0938-4682-ab7e-2e1cacd30296
-- title:
--   Finite mapped original counting mass yields finitely many source times in the restricted preimage
-- statement:
--   For an actual source counting measure restricted to a jump-time set A and mapped to time-mark pairs, finite mass on a measurable target band B implies only finitely many original times belong to A and map into B. This is a direct bridge from the Proved intrinsic stopped jump-count finiteness to finite physical jump-cell isolation.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.map_apply, restrict_apply, count_apply_lt_top at commit 0df444a360eaa60ab8c11dca51a86af692955474; source original stopped count theorem 84c8c695-3b46-4cb3-9780-38ba045dc5a9; 11 November 2026.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_bva54_restricted_mapped_count_finite_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] (A : Set α) (f : α → β) (hf : Measurable f) (B : Set β) (hB : MeasurableSet B) (hFinite : ((Measure.count.restrict A).map f) B < ⊤) : (A ∩ f ⁻¹' B).Finite := by sorry
