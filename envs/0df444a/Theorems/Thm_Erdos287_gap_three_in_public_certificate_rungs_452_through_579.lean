-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_public_certificate_rungs_452_through_579
-- name    : Erdos287.gap_three_in_public_certificate_rungs_452_through_579
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:58:08.640636+00:00
-- url     : https://prove2.me/theorems/ad575dc7-dd61-5b3e-b49c-e0f0abb9eeb5
-- title:
--   Erdős 287 public certificate rungs 452 through 579
-- statement:
--   In a strictly increasing unit-fraction representation of one, at least one consecutive gap is at least three if the maximum lies in the certified interval from public certificate rungs 452 through 579. The Lean statement gives both endpoints exactly.
-- source:
--   Public rung table for Erdős #287, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/data/rungs_extended.json.

import Mathlib

theorem Erdos287.gap_three_in_public_certificate_rungs_452_through_579 (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 628919486063281440635202976521062403432595061354388928363545825841263440810338906996674850311983730757157126470214095283143956934526967504054074111537354822267076891450829805233739745763600448812851418520291971663867976874379044805453494265712731085943499445304764813311688769692043498937107096292386569754873653176648150890472810741770 < f (k - 1))
    (hhi : f (k - 1) ≤ 23805813089741725182015384511104054621492462436169819393247337376348590232433101934819416759323635460150661347734096238203216931254112393534809041441592068475628301049051124656934967823564632980768629149462335397517232454001292587002419225988306705758498861462117908174471405321846075615650603757483916563126131761186680416886434814622774540866409197191052369809358145986408103616184330) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
