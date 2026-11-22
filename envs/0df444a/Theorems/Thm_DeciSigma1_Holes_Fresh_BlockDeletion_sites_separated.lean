-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_sites_separated
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.sites_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:04.885725+00:00
-- url     : https://prove2.me/theorems/243b1d55-8e96-42c5-8c5f-2c8f6695b291
-- title:
--   Block Deletion: sites separated
-- statement:
--   Two deletion sites of one word lie in different upper blocks, so the earlier site ends
--   strictly before the later one starts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L548-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L548-L560

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.sites_separated {l : Fin k} {c c' : ℕ} (hc : c ∈ m.sites l)
    (hc' : c' ∈ m.sites l) (hlt : c < c') : c + m.deletionLength < c' := by sorry
