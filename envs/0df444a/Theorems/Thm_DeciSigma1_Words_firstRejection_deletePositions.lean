-- Prove2me | Theorems.Thm_DeciSigma1_Words_firstRejection_deletePositions
-- name    : DeciSigma1.Words.firstRejection_deletePositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:21.311458+00:00
-- url     : https://prove2.me/theorems/5a0eb314-4047-4909-8dad-47201cd17859
-- title:
--   Words: first Rejection delete Positions
-- statement:
--   Deleting loops of the run of an eligible coordinate moves its first rejected cut to the
--   image of that cut: rejection is monotone along an eligible run, so no assumption on the deleted
--   positions other than the states of the edited run is needed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L372-L397
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L372-L397

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}

theorem DeciSigma1.Words.firstRejection_deletePositions (M : StructuralReader α S k) {W U : Fin k → List α}
    {i : Fin k} (hW : M.Eligible W i) (hU : U i = deletePositions (W i) D)
    (hD : (W i).length ∉ D)
    (hrun : ∀ a, M.runPrefix U i a = M.runPrefix W i (greatestPreimage D a)) :
    M.firstRejection U i = retainedCount D (M.firstRejection W i) := by sorry
