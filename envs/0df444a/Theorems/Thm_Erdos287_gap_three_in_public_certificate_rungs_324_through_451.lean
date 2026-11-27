-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_public_certificate_rungs_324_through_451
-- name    : Erdos287.gap_three_in_public_certificate_rungs_324_through_451
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:57:11.75617+00:00
-- url     : https://prove2.me/theorems/9f250f8c-ddcc-465a-ac60-198a375988df
-- title:
--   Erdős 287 public certificate rungs 324 through 451
-- statement:
--   Let $1<n_1<\cdots<n_k$ be integers whose reciprocals sum to one. The exact interval in the Lean statement consists of rungs 324 through 451 of the public Erdős #287 certificate table. If the largest denominator belongs to this interval, at least one consecutive gap is at least three.
-- source:
--   Public rung table for Erdős #287, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/data/rungs_extended.json. Compact certificate reconstruction and exact interval verification.

import Mathlib

theorem Erdos287.gap_three_in_public_certificate_rungs_324_through_451 (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435 < f (k - 1))
    (hhi : f (k - 1) ≤ 628919486063281440635202976521062403432595061354388928363545825841263440810338906996674850311983730757157126470214095283143956934526967504054074111537354822267076891450829805233739745763600448812851418520291971663867976874379044805453494265712731085943499445304764813311688769692043498937107096292386569754873653176648150890472810741770) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
