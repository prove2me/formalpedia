-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_const_triple
-- name    : DeciSigma1.Holes.Tail.exists_const_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:30.893011+00:00
-- url     : https://prove2.me/theorems/fc9e662e-5feb-4549-9442-d3bbf779da9f
-- title:
--   Tail: exists const triple
-- statement:
--   For finitely many monotone predicates on levels, one of the triples `{3j, 3j+1, 3j+2}` with
--   `j ≤ |ι|` sees no change of any of them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L686-L713
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L686-L713

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

theorem DeciSigma1.Holes.Tail.exists_const_triple {ι : Type} [Fintype ι] (P : ι → ℕ → Prop)
    (hmono : ∀ x l, P x l → P x (l + 1)) :
    ∃ j, j ≤ Fintype.card ι ∧ ∀ x, (P x (3 * j) ↔ P x (3 * j + 2)) := by sorry
