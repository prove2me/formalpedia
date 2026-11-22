-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_le_exp2
-- name    : DeciSigma1.Holes.Tail.suffixLengthBound_le_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:00.668017+00:00
-- url     : https://prove2.me/theorems/49ab4ef2-f3fe-4ed5-ad90-83a006ec5cf5
-- title:
--   Tail: suffix Length Bound le exp2
-- statement:
--   The suffix search has a logarithmic bound whose slope depends only on the number of
--    targets and their common chain budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/LevelElementaryBound.lean#L90-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/LevelElementaryBound.lean#L90-L136

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic

theorem DeciSigma1.Holes.Tail.suffixLengthBound_le_exp2 (m N S j b t : ℕ) (hb : b + 2 ≤ exp2 t) :
    suffixLengthBound m N (List.replicate j S) b + b + 2 ≤
      exp2 (exp2 ((m + N + 10) * (S + 3) ^ j) * t) := by sorry
