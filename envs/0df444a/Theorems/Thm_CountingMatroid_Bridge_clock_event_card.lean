-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_clock_event_card
-- name    : CountingMatroid.Bridge.clock_event_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:17:43.536628+00:00
-- url     : https://prove2.me/theorems/a6271382-7389-4389-ada7-5455e9d8df1d
-- title:
--   Exact event cardinality for injectively sampled clock positions
-- statement:
--   For any injection of K coin positions into B clock steps and any event on K Boolean samples, the number of B-bit clock tapes whose sampled bits satisfy the event equals the event cardinality times 2^(B-K). Split a clock tape into its restriction to the chosen positions and its restriction to the complement. This is a bijection; an event constrains only the first component, while the complement has exactly B-K Boolean coordinates. This handles unused clock bits without assuming consecutive coin flips.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge

/-- Restricting a uniformly chosen clock tape to any fixed injective set of
coin positions multiplies every event's cardinality by exactly `2^(B-K)`. -/
theorem CountingMatroid.Bridge.clock_event_card {K B : ℕ} (e : Fin K ↪ Fin B) (event : (Fin K → Bool) → Prop) :
    Nat.card {bits : Fin B → Bool // event (fun i => bits (e i))} =
      Nat.card {bits : Fin K → Bool // event bits} * 2^(B-K) := by
  sorry
