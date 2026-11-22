-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_levelState_envelope
-- name    : DeciSigma1.Holes.Tail.levelState_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:03.331563+00:00
-- url     : https://prove2.me/theorems/8951bb2a-7b4c-4a9a-8c53-464ea2517756
-- title:
--   Tail: level State envelope
-- statement:
--   Every iterate of the level recursion satisfies the same logarithmic envelope.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/LevelElementaryBound.lean#L246-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/LevelElementaryBound.lean#L246-L266

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

theorem DeciSigma1.Holes.Tail.levelState_envelope (k N A l : ℕ)
    (hA : k + N + levelMultiplicity k N + N * N + 20 ≤ A) :
    stateEnvelope
      (exp2 (((k + N + 10) * (levelMultiplicity k N + N + 3) ^ k + 5) * l) * A)
      (levelState k N l) := by sorry
