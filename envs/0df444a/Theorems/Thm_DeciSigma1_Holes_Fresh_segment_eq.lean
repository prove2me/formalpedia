-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_segment_eq
-- name    : DeciSigma1.Holes.Fresh.segment_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:36.851813+00:00
-- url     : https://prove2.me/theorems/03573c40-a854-44ec-9dee-79c779386932
-- title:
--   Fresh: segment eq
-- statement:
--   A text segment of a word, read through a window of it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L357-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L357-L359

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
omit [DecidableEq α]

theorem DeciSigma1.Holes.Fresh.segment_eq {x z : List α} {p n r r' : ℕ} (hz : (x.drop p).take n = z) (h1 : r' ≤ r)
    (h2 : r ≤ n) : (x.drop (p + r')).take (r - r') = (z.drop r').take (r - r') := by sorry
