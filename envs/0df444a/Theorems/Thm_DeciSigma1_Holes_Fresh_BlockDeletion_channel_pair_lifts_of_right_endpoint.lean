-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_channel_pair_lifts_of_right_endpoint
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.channel_pair_lifts_of_right_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:12.300519+00:00
-- url     : https://prove2.me/theorems/2fa8e6bc-f691-4af2-844e-77b6147837e3
-- title:
--   Block Deletion: channel pair lifts of right endpoint
-- statement:
--   A comparison whose end lies strictly inside the upper block of a host junction gives a pair
--   of the original channel. The target suffix is original text in the last marker of its word, the
--   comparison starts at most `windowLength` letters left of the junction, by the factor antichain
--   property, and the equal label window before the right cut of the deletion gives the original
--   pair.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L391-L568
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L391-L568

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.channel_pair_lifts_of_right_endpoint [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {i j : Fin k} {a b L d : ℕ} (hL : (m.apply j).length = b + L)
    (hpre : (m.apply j).drop b <+: (m.apply i).drop a) (hd0 : 0 < d) (hdL : d < L)
    (hJ : IsJunction m.deletionLength (m.sites i) (a + d)) (hlt : L < d + m.upperCutLength) :
    (T.runPrefix m.apply i a, T.runPrefix m.apply j b) ∈ T.channel W i j := by sorry
