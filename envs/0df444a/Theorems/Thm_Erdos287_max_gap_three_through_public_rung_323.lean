-- Prove2me | Theorems.Thm_Erdos287_max_gap_three_through_public_rung_323
-- name    : Erdos287.max_gap_three_through_public_rung_323
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:58:50.210607+00:00
-- url     : https://prove2.me/theorems/390fc943-24eb-4470-82b2-a179beec0d44
-- title:
--   Erdős 287 continuous range through public certificate rung 323
-- statement:
--   Let the denominators of an exact unit-fraction representation of one be strictly increasing integers greater than one. If the largest denominator is at most the exact right endpoint of rung 323 in the public certificate table, approximately $7.2081163\times10^{285}$, then at least one consecutive gap is at least three.
-- source:
--   Erdős Problem 287, assembled finite interval certificates.

import Mathlib

theorem Erdos287.max_gap_three_through_public_rung_323 (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
