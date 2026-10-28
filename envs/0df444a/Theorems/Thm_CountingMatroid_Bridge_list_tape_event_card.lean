-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_list_tape_event_card
-- name    : CountingMatroid.Bridge.list_tape_event_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:18:01.914405+00:00
-- url     : https://prove2.me/theorems/85501542-bb5b-4cc7-823f-54600424e81a
-- title:
--   List and finite-function Boolean tapes have identical event counts
-- statement:
--   For every predicate on Boolean lists, the number of satisfying lists of length K equals the number of Fin K to Bool functions whose List.ofFn satisfies the predicate. The bijection sends a function to its list of values and a length-K list to its indexed entries. This bridges the source library's list-tape cardinality with the mission's finite-function tapes.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge

/-- Convert an event on lists of exactly K bits to the same event on Fin K tapes. -/
theorem CountingMatroid.Bridge.list_tape_event_card (K : ℕ) (event : List Bool → Prop) :
    Set.ncard {xs : List Bool | xs.length = K ∧ event xs} =
      Nat.card {bits : Fin K → Bool // event (List.ofFn bits)} := by
  sorry
