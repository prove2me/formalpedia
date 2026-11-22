-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_not_in_labelWindow
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.junction_not_in_labelWindow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:08.279807+00:00
-- url     : https://prove2.me/theorems/070fab21-3d1d-435d-ac32-afd393af5a54
-- title:
--   Block Deletion: junction not in label Window
-- statement:
--   No junction of a word lies in the `windowLength` letters before the junction of a site: an
--   earlier site ends before the label window, and a later site has a later junction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L300-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L300-L339

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.junction_not_in_labelWindow [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l : Fin k} {c J' : ℕ} (hc : c ∈ m.sites l)
    (hJ' : IsJunction m.deletionLength (m.sites l) J')
    (h1 : retainedCount (sitePositions m.deletionLength (m.sites l)) c -
      windowLength W t (W l) c < J')
    (h2 : J' < retainedCount (sitePositions m.deletionLength (m.sites l)) c) : False := by sorry
