-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_relAnchors_iff
-- name    : DeciSigma1.Holes.Fresh.mem_relAnchors_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:41.277167+00:00
-- url     : https://prove2.me/theorems/a59bbc2e-507d-49c4-b6d7-9397d8f11459
-- title:
--   Fresh: mem rel Anchors iff
-- statement:
--   Membership in `relativeAnchors` for a text that is a window of a word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L394-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L394-L402

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.mem_relAnchors_iff {W : Fin k → List α} {t : ℕ} {x z : List α} {c n q : ℕ}
    (hz : (x.drop c).take n = z) (hcn : c + n ≤ x.length) (hq1 : 1 ≤ q) (hqn : q ≤ n) :
    q ∈ relativeAnchors W t (x.take c) z ↔ c + q ∈ contextAnchors W t x := by sorry
