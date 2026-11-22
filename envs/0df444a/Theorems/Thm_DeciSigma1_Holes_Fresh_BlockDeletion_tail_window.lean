-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_tail_window
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.tail_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:07.777799+00:00
-- url     : https://prove2.me/theorems/5356211d-cef9-4186-ad29-c71f546407fd
-- title:
--   Block Deletion: tail window
-- statement:
--   The edited text of a word ends with its original terminal window: past the last site, the
--   cut map is a shift.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L343-L384
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L343-L384

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.tail_window {l : Fin k} {P : ℕ}
    (hP : ∀ c ∈ m.sites l, c + m.deletionLength + P ≤ (W l).length) (hPl : P ≤ (W l).length)
    {b' : ℕ} (hb1 : (m.apply l).length - P ≤ b') (hb2 : b' ≤ (m.apply l).length) :
    (m.apply l).drop b' = (W l).drop ((W l).length - ((m.apply l).length - b')) ∧
      greatestPreimage (sitePositions m.deletionLength (m.sites l)) b' = (W l).length -
          ((m.apply l).length - b') := by sorry
