-- Prove2me | Theorems.Thm_Finset_mem_pairs
-- name    : Finset.mem_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:50.200692+00:00
-- url     : https://prove2.me/theorems/93b4b033-8d12-4e7d-8a51-b07ded14be92
-- title:
--   Finset: mem pairs
-- statement:
--   `s(v, w)` is a pair of `s` when `v` and `w` are distinct elements of `s`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L69-L70
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L69-L70

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_RandomGraph
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {V : Type*} [DecidableEq V]

theorem Finset.mem_pairs {s : Finset V} {v w : V} : s(v, w) ∈ s.pairs ↔ v ∈ s ∧ w ∈ s ∧ v ≠ w := by sorry
