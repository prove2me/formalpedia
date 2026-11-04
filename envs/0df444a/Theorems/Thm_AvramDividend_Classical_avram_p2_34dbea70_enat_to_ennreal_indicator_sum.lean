-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_enat_to_ennreal_indicator_sum
-- name    : AvramDividend.Classical.avram_p2_34dbea70_enat_to_ennreal_indicator_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:28:50.229857+00:00
-- url     : https://prove2.me/theorems/9fe3d263-414f-40c5-bc7b-b08709a29273
-- title:
--   Conversion of finite ENat marked indicator sums to ENNReal preserves the exact count
-- statement:
--   For any finite index set and decidable mark predicate, converting the ENat sum of its zero-one marked indicators into ENNReal gives exactly the ENNReal sum of the same indicators. This finite additive homomorphism identity, proved without any finite-activity assumption for the underlying path, joins the pathwise ENat jump liminf to the ENNReal integrands of the genuine original-process grid expectation and Fatou bridge.

import Mathlib

open Finset
open scoped ENat ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_enat_to_ennreal_indicator_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (marked : α → Prop) [DecidablePred marked] :
    ENat.toENNReal
      (∑ i ∈ s, (if marked i then (1 : ℕ∞) else 0)) =
        ∑ i ∈ s, (if marked i then (1 : ℝ≥0∞) else 0) := by sorry
