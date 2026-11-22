-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_order
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.site_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:13.149793+00:00
-- url     : https://prove2.me/theorems/f24cde77-1eeb-4034-a54c-aa341b5281d9
-- title:
--   Block Deletion: site order
-- statement:
--   Of two sites of one word, the upper block of the earlier one ends before that of the later one
--   starts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L103-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L103-L112

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.site_order {o o' : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (ho' : o' ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) (hth' : m.edge.TraversedBy o')
        (hl : o.1 = o'.1)
    (hlt : depthCut W t o m.maxDepth < depthCut W t o' m.maxDepth) : o.2.2 ≤ o'.2.1 := by sorry
