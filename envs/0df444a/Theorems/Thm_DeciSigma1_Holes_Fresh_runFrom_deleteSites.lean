-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_runFrom_deleteSites
-- name    : DeciSigma1.Holes.Fresh.runFrom_deleteSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:52.388793+00:00
-- url     : https://prove2.me/theorems/7e25905d-9aa2-49a1-87a4-6f39eb5852d3
-- title:
--   Fresh: run From delete Sites
-- statement:
--   If every deleted text starts and ends in the same state, the state of the edited text at a
--   cut is the state of the original text at the greatest preimage of the cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L344-L354
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L344-L354

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}
variable {S : Type}
omit [DecidableEq α]

theorem DeciSigma1.Holes.Fresh.runFrom_deleteSites (T : Table α S k) (q0 : S) {x : List α} (hs : StrictlySeparated δ cs)
    (hst : ∀ c ∈ cs, c + δ < x.length ∧
      runFrom T.step q0 (x.take c) = runFrom T.step q0 (x.take (c + δ)))
    (a : ℕ) :
    runFrom T.step q0 ((deletePositions x (sitePositions δ cs)).take a) =
      runFrom T.step q0 (x.take (greatestPreimage (sitePositions δ cs) a)) := by sorry
