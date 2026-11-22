-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_window
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.junction_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:43.072425+00:00
-- url     : https://prove2.me/theorems/e9d4486b-bc2a-4e26-a292-838f156ffd71
-- title:
--   Block Deletion: junction window
-- statement:
--   At the junction `J` of a site `c`, the greatest preimage is `c + δ`, the next
--   `upperCutLength` letters are original text up to the end of the upper block, and no other
--   junction of the word lies in `(J, J + upperCutLength)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L215-L276
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L215-L276

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.junction_window {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    greatestPreimage (sitePositions m.deletionLength (m.sites l))
        (retainedCount (sitePositions m.deletionLength (m.sites l)) c) = c + m.deletionLength ∧
    (∀ J', IsJunction m.deletionLength (m.sites l) J' →
      J' ≤ retainedCount (sitePositions m.deletionLength (m.sites l)) c ∨
        retainedCount (sitePositions m.deletionLength (m.sites l)) c + m.upperCutLength ≤ J') ∧
    retainedCount (sitePositions m.deletionLength (m.sites l)) c + m.upperCutLength ≤
      (m.apply l).length ∧
    ((m.apply l).drop (retainedCount (sitePositions m.deletionLength (m.sites l)) c)).take
        m.upperCutLength =
      ((W l).drop (c + m.deletionLength)).take m.upperCutLength := by sorry
