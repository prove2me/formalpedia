-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_label_window
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.label_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:06.195999+00:00
-- url     : https://prove2.me/theorems/569f3399-3dad-4a9b-a251-75b376ed714a
-- title:
--   Block Deletion: label window
-- statement:
--   Equal labels at two cuts give the same text and the same states on the last
--   `windowLength` letters before both cuts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L220-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L220-L250

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
omit [Fintype S]

theorem DeciSigma1.Holes.Fresh.BlockDeletion.label_window {l : Fin k} {c c' : ℕ} (hc : c ≤ (W l).length) (hc' : c' ≤ (W l).length)
    (h : label T W t l c = label T W t l c') {e : ℕ} (he : e ≤ windowLength W t (W l) c) :
    e ≤ c ∧ e ≤ c' ∧ ((W l).drop (c - e)).take e = ((W l).drop (c' - e)).take e ∧
      T.runPrefix W l (c - e) = T.runPrefix W l (c' - e) := by sorry
