-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_finite_good_card_of_bad_bound
-- name    : CountingMatroid.Bridge.finite_good_card_of_bad_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:20:02.173575+00:00
-- url     : https://prove2.me/theorems/ad8f5f52-a78b-4fb3-9fcb-23980cdf220c
-- title:
--   Convert the source bad-event probability into the mission success count
-- statement:
--   If the ENNReal cardinality of failing length-K lists times (1/2)^K is at most a nonnegative rational delta, then at least (1-delta)*2^K finite Boolean tapes satisfy the complementary good event. First use the list/function bijection. Map the finite ENNReal inequality to real numbers and then rationals, multiply by the positive number 2^K, and subtract the bad count from the total 2^K tapes. No computational implementation is assumed in this counting lemma.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_list_tape_event_card

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge

/-- Convert the source's ENNReal bad-event bound into the mission's rational
lower bound on the number of successful finite tapes. -/
theorem CountingMatroid.Bridge.finite_good_card_of_bad_bound (K : ℕ) (δ : ℚ) (hδ : 0 ≤ δ)
    (good : List Bool → Prop)
    (hbad : (Set.ncard {xs : List Bool | xs.length = K ∧ ¬good xs} : ENNReal) *
      (1/2 : ENNReal)^K ≤ ENNReal.ofReal (δ : ℝ)) :
    (1-δ) * (2:ℚ)^K ≤ Nat.card {bits : Fin K → Bool // good (List.ofFn bits)} := by
  sorry
