-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_pieceLengthBound_mono
-- name    : DeciSigma1.Holes.Tail.pieceLengthBound_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:38.224077+00:00
-- url     : https://prove2.me/theorems/192e754b-ed3a-49a6-bafd-c37afafd24e6
-- title:
--   Tail: piece Length Bound mono
-- statement:
--   The split cap is monotone in the period.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L349-L358
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L349-L358

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.pieceLengthBound_mono {N d d' h t : ℕ} (hd : d ≤ d') :
    pieceLengthBound N d h t ≤ pieceLengthBound N d' h t := by sorry
