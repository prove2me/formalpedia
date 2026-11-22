-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_two_d_le_boundaryMargin
-- name    : DeciSigma1.Holes.Periodic.two_d_le_boundaryMargin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:50.976774+00:00
-- url     : https://prove2.me/theorems/27e18b8b-69f9-45ff-9c00-9a1fdc49eb38
-- title:
--   Periodic: two d le boundary Margin
-- statement:
--   The Periodic construction uses the two d le boundary Margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L80-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L80-L83

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

theorem DeciSigma1.Holes.Periodic.two_d_le_boundaryMargin {N : ℕ} (hN : 0 < N) (d : ℕ) : 2 * d ≤ boundaryMargin N d := by sorry
