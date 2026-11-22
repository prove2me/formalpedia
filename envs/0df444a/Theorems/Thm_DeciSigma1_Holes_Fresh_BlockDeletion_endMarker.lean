-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_endMarker
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.endMarker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:41.136801+00:00
-- url     : https://prove2.me/theorems/902ee46c-98d3-488d-9dc3-2574518ddc61
-- title:
--   Block Deletion: end Marker
-- statement:
--   The marker of level `t + 1` that ends a traversing occurrence lies within its last
--   `minDepth` lower blocks, by the bound on anchors inside a marker and the deletion margin.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L174-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L174-L202

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.endMarker [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) :
    ∃ g ∈ active W (t + 1), marker W (t + 1) g <:+ (W o.1).take o.2.2 ∧
      (marker W (t + 1) g).length ≤ m.upperCutLength := by sorry
