-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_public_certificate_rungs_68_through_323
-- name    : Erdos287.gap_three_in_public_certificate_rungs_68_through_323
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:52:35.569456+00:00
-- url     : https://prove2.me/theorems/657af938-ebe1-4bcf-aea3-7172a6a309a7
-- title:
--   Erdős 287 public certificate rungs 68 through 323
-- statement:
--   Let $1<n_1<\cdots<n_k$ be integers whose reciprocals sum to one. The exact interval in the Lean statement consists of rungs 68 through 323 of the public Erdős #287 certificate table. If the largest denominator belongs to this interval, at least one consecutive gap is at least three.
-- source:
--   Public rung table for Erdős #287, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/data/rungs_extended.json. Compact certificate reconstruction and exact interval verification.

import Mathlib

theorem Erdos287.gap_three_in_public_certificate_rungs_68_through_323 (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 127121066678798445735243883196317776949351426878578394099564929136550843411572772149955019782860736757937532214437526600769419124790518099200969633104128306711796545988048739553341603835 < f (k - 1))
    (hhi : f (k - 1) ≤ 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
