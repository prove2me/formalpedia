-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_firstRejection_sub_lt_word
-- name    : DeciSigma1.Holes.Tail.firstRejection_sub_lt_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:42.768531+00:00
-- url     : https://prove2.me/theorems/ec94e59d-6ac3-4731-b76b-ac3d04cde8b2
-- title:
--   Tail: first Rejection sub lt word
-- statement:
--   An interval of period `p` that starts at `s ≤ J` and reaches the first rejected cut `J`
--   satisfies `J - s < N · p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L526-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L526-L560

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
variable {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k}

theorem DeciSigma1.Holes.Tail.firstRejection_sub_lt_word [Fintype S] (h : M.Eligible W i) {p s e : ℕ} (hp : 0 < p)
    (hper : PeriodicOn (W i) p s e) (hsJ : s ≤ M.firstRejection W i)
        (hJe : M.firstRejection W i ≤ e) :
    M.firstRejection W i - s < Fintype.card S * p := by sorry
