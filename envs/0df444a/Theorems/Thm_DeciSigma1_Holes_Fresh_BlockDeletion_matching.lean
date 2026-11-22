-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_matching
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:49.102825+00:00
-- url     : https://prove2.me/theorems/93c6ca5a-ce09-4a3e-b02a-bff41452ef11
-- title:
--   Block Deletion: matching
-- statement:
--   In a comparison of edited texts in which every host junction strictly inside has the rest
--   of its upper block inside the comparison, the host and target junctions strictly inside
--   correspond. The proof is an induction on the rightmost junction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L57-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L57-L107

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.matching [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {i j : Fin k} {a b L : ℕ} (hL : (m.apply j).length = b + L)
    (hpre : (m.apply j).drop b <+: (m.apply i).drop a)
    (hB : ∀ d,
        0 < d → d < L → IsJunction m.deletionLength (m.sites i)
            (a + d) → d + m.upperCutLength ≤ L) :
    ∀ d, 0 < d → d < L →
      (IsJunction m.deletionLength (m.sites i) (a + d) ↔ IsJunction m.deletionLength
          (m.sites j) (b + d)) := by sorry
