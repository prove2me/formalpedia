-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_anchor_ne_site
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.anchor_ne_site
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:18.564524+00:00
-- url     : https://prove2.me/theorems/0d5867f4-e9ee-4f5d-875a-e68ddb572819
-- title:
--   Block Deletion: anchor ne site
-- statement:
--   Upper anchors are not cuts of a site: sites lie strictly inside upper blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L205-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L205-L210

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.anchor_ne_site {l : Fin k} {p c : ℕ}
    (hp : p ∈ anchors W (t + 1) l) (hc : c ∈ m.sites l) : p ≠ c ∧ p ≠ c + m.deletionLength := by sorry
