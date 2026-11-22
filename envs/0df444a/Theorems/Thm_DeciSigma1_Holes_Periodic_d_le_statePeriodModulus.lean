-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_statePeriodModulus
-- name    : DeciSigma1.Holes.Periodic.d_le_statePeriodModulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:37.198837+00:00
-- url     : https://prove2.me/theorems/8a35c295-0575-4584-9328-fd483662585d
-- title:
--   Periodic: d le state Period Modulus
-- statement:
--   The Periodic construction uses the d le state Period Modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L74-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L74-L75

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Periodic.d_le_statePeriodModulus (N d : ℕ) :
    d ≤ statePeriodModulus N d := by sorry
