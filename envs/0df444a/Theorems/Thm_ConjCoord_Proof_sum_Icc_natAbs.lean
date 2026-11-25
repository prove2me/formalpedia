-- Prove2me | Theorems.Thm_ConjCoord_Proof_sum_Icc_natAbs
-- name    : ConjCoord.Proof.sum_Icc_natAbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:42.818537+00:00
-- url     : https://prove2.me/theorems/0d0fad71-a5c8-4dc1-9e12-3805896d22de
-- title:
--   Proof: sum Icc nat Abs
-- statement:
--   The Proof construction uses the sum Icc nat Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L93-L107
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L93-L107

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.sum_Icc_natAbs {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ x ∈ Icc (-(n : ℤ)) n, f x.natAbs = ∑ k ∈ range (n + 1), wt k • f k := by sorry
