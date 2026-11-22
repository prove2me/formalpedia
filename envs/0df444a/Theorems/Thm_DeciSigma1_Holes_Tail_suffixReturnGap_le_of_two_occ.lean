-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixReturnGap_le_of_two_occ
-- name    : DeciSigma1.Holes.Tail.suffixReturnGap_le_of_two_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:32.090809+00:00
-- url     : https://prove2.me/theorems/8215b97c-8221-48ea-b42a-d58e4fae4505
-- title:
--   Tail: suffix Return Gap le of two occ
-- statement:
--   An occurrence of `v_{b+h}(t)` ending `h` letters after an occurrence of `v_b(t)`, with `h` at
--   most the window gap, gives `suffixReturnGap t b ≤ h`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L143-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L143-L164

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]

theorem DeciSigma1.Holes.Tail.suffixReturnGap_le_of_two_occ {x t : List α} {b g e e' : ℕ}
    (he : e ∈ occurrences x t (b + g))
    (he' : e' ∈ occurrences x t b) (hlt : e' < e) (hgap : e - e' ≤ g) :
    ∃ h, suffixReturnGap t b = some h ∧ h ≤ e - e' := by sorry
