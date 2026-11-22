-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_sep
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.junction_sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:52.368235+00:00
-- url     : https://prove2.me/theorems/dc980d9f-a3a1-410d-9662-fd87e823e645
-- title:
--   Block Deletion: junction sep
-- statement:
--   Two junctions of one word are at least `upperCutLength` apart.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L599-L606
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L599-L606

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.junction_sep {l : Fin k} {u u' : ℕ} (hu : IsJunction m.deletionLength (m.sites l) u)
        (hu' : IsJunction m.deletionLength (m.sites l) u')
        (hlt : u < u') :
    u + m.upperCutLength ≤ u' := by sorry
