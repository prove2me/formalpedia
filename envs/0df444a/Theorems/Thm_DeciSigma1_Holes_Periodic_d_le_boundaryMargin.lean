-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
-- name    : DeciSigma1.Holes.Periodic.d_le_boundaryMargin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:25.601678+00:00
-- url     : https://prove2.me/theorems/d9d11787-3106-44aa-a7d7-e9acc2e214b6
-- title:
--   Periodic: d le boundary Margin
-- statement:
--   The Periodic construction uses the d le boundary Margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L77-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L77-L78

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

theorem DeciSigma1.Holes.Periodic.d_le_boundaryMargin (N d : ℕ) : d ≤ boundaryMargin N d := by sorry
