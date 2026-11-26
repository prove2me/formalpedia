-- Prove2me | Theorems.Thm_CSeparatedNPComplete_majorized_sum_convex_le
-- name    : CSeparatedNPComplete.majorized.sum_convex_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:49.212702+00:00
-- url     : https://prove2.me/theorems/b2a03b5b-4f99-48bb-8c99-79124d401764
-- title:
--   majorized: sum convex le
-- statement:
--   Karamata's inequality with mathlib's native convexity hypothesis.
--   In the source convention, `majorized u v` means that `u` majorizes `v`.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Karamata.lean#L21-L37
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Karamata.lean#L21-L37

module
public import Definitions.Def_CSeparatedNPComplete_ConvexPredicate
public import Definitions.Def_CSeparatedNPComplete_ConvexSlopes
public import Definitions.Def_CSeparatedNPComplete_WeightedSum
public import Definitions.Def_CSeparatedNPComplete_Karamata
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.majorized.sum_convex_le {n : Nat} {u v : Vec n}
    (hmajorized : majorized u v) {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hu_mem : ∀ i, u i ∈ s) (hv_mem : ∀ i, v i ∈ s) :
    vecSum (fun i => f (v i)) ≤ vecSum (fun i => f (u i)) := by sorry
