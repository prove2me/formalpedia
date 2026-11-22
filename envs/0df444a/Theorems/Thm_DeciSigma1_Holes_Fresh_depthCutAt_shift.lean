-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_shift
-- name    : DeciSigma1.Holes.Fresh.depthCutAt_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:28.189463+00:00
-- url     : https://prove2.me/theorems/a6a99d4f-c79c-47d4-9c02-8bc26c62aad4
-- title:
--   Fresh: depth Cut At shift
-- statement:
--   Cuts read from the right agree under a shift, as long as the two anchor sets agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L303-L337
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L303-L337

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

theorem DeciSigma1.Holes.Fresh.depthCutAt_shift {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) (hlo : lo ∈ Q) (hn : n ∈ Q)
    (hlon : lo ≤ n) : ∀ d ≤ anchorCount Q lo n, depthCutAt A (base + n) d = base +
        depthCutAt Q n d := by sorry
