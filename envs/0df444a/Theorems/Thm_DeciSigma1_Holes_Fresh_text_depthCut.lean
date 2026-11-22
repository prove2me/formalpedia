-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_text_depthCut
-- name    : DeciSigma1.Holes.Fresh.text_depthCut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:35.169795+00:00
-- url     : https://prove2.me/theorems/4a8b95a2-9998-4e96-bacc-41a488f75bf1
-- title:
--   Fresh: text depth Cut
-- statement:
--   The text between two depth cuts of an upper occurrence is the concatenation of the
--   corresponding lower blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L363-L386
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L363-L386

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.text_depthCut {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d d' : ℕ} (hdd : d ≤ d')
    (hd' : d' ≤ lowerBlockCount W t o) :
    ((W o.1).drop (depthCut W t o d')).take (depthCut W t o d - depthCut W t o d') =
      (((reversedBlocks W t o).take d').drop d).reverse.flatten := by sorry
