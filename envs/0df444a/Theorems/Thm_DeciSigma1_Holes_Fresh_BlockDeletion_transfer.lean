-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_transfer
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:54.80216+00:00
-- url     : https://prove2.me/theorems/2e6b283f-5dec-45cc-ab29-2318f1f221bd
-- title:
--   Block Deletion: transfer
-- statement:
--   Let `u₁` be a junction of word `l₁`, and let the edited word `l₂` have the same text of
--   `upperCutLength` letters from `u₂`, with no junction strictly inside. Then `u₂` is a junction of
--   `l₂`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L534-L596
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L534-L596

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.transfer [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l₁ l₂ : Fin k} {u₁ u₂ : ℕ} (hJ : IsJunction m.deletionLength (m.sites l₁) u₁)
    (htext : ((m.apply l₁).drop u₁).take m.upperCutLength =
        ((m.apply l₂).drop u₂).take m.upperCutLength)
    (hfree : ∀ J,
        IsJunction m.deletionLength (m.sites l₂) J → ¬ (u₂ < J ∧ J < u₂ + m.upperCutLength))
    (hlen : u₂ + m.upperCutLength ≤ (m.apply l₂).length) :
    IsJunction m.deletionLength (m.sites l₂) u₂ := by sorry
