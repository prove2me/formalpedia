-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_valid
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.site_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:11.02626+00:00
-- url     : https://prove2.me/theorems/4fc05413-cfd5-4795-b357-a32eefb67908
-- title:
--   Block Deletion: site valid
-- statement:
--   Every site satisfies the hypotheses of `contextAnchors_deleteSite` and is a loop of the run.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L567-L594
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L567-L594

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
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.site_valid {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    ValidDeletionSite W t (W l) c m.deletionLength ∧ c + m.deletionLength < (W l).length ∧
      runFrom T.step (T.start l) ((W l).take c) =
          runFrom T.step (T.start l) ((W l).take (c + m.deletionLength)) := by sorry
