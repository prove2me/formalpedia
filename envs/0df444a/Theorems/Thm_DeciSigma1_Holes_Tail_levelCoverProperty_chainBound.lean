-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_levelCoverProperty_chainBound
-- name    : DeciSigma1.Holes.Tail.levelCoverProperty_chainBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:44.309016+00:00
-- url     : https://prove2.me/theorems/f2c89376-da8a-424d-95eb-4b911f8326d9
-- title:
--   Tail: level Cover Property chain Bound
-- statement:
--   A word with the level cover property at level `m` has suffix chains of at most
--   `chainLengthBound m + N` members. The members are counted by their suffix starts: at most
--   `N - 1` at or before the first rejected cut, one empty suffix, the uncovered positions of the
--   rejected tail, fewer than `terminalLengthBound m` in the periodic suffix, and at most twice the
--   period for each factor of the cover.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L780-L940
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L780-L940

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]
omit [DecidableEq S]

theorem DeciSigma1.Holes.Tail.levelCoverProperty_chainBound (C : LevelBounds σ k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} {m : ℕ} (h : M.Eligible W i)
        (hK : LevelCoverProperty C m M W i) :
    ChainBound (W i) (C.chainLengthBound m + Fintype.card S) := by sorry
