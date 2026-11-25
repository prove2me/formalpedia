-- Prove2me | Theorems.Thm_ConjCoord_Proof_card_zfilter
-- name    : ConjCoord.Proof.card_zfilter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:44.625579+00:00
-- url     : https://prove2.me/theorems/cd7fbc09-06f8-420c-837a-e40bd2680811
-- title:
--   Proof: card zfilter
-- statement:
--   The Proof construction uses the card zfilter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L34-L91
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L34-L91

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.card_zfilter (c : ℕ) (hc : 0 < c) (n : ℕ) (r : ℤ) (hr : r ≤ n) :
    ((Icc (-(n : ℤ)) n).filter fun z => (c : ℤ) * z ^ 2 = r).card =
      if 0 ≤ r then zc c r.toNat else 0 := by sorry
