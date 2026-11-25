-- Prove2me | Theorems.Thm_Finset_pairs_mono
-- name    : Finset.pairs_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:00:07.879243+00:00
-- url     : https://prove2.me/theorems/d53c3b8b-7e8b-4ffc-9a2a-f6aa1de9875a
-- title:
--   Finset: pairs mono
-- statement:
--   The pairs of a subset are pairs of the superset.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L73-L74
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L73-L74

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

theorem Finset.pairs_mono {s t : Finset V} (h : s ⊆ t) : s.pairs ⊆ t.pairs := by sorry
