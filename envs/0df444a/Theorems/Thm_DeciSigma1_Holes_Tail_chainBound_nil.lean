-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_chainBound_nil
-- name    : DeciSigma1.Holes.Tail.chainBound_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:31.244472+00:00
-- url     : https://prove2.me/theorems/e877fcc9-3c3f-411d-9661-ce46aa1d8ae2
-- title:
--   Tail: chain Bound nil
-- statement:
--   The empty word has every chain budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L134-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L134-L135

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.chainBound_nil [DecidableEq α] (S : ℕ) : ChainBound ([] : List α) S := by sorry
