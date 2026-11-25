-- Prove2me | Theorems.Thm_Finset_card_pairs
-- name    : Finset.card_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:00:22.494737+00:00
-- url     : https://prove2.me/theorems/be9bddf9-a06b-4843-952c-822b5ff0a682
-- title:
--   Finset: card pairs
-- statement:
--   A set of size `n` has `C(n, 2)` pairs of distinct elements (Mathlib's
--   `Sym2.card_image_offDiag`).
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L93-L94
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L93-L94

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

theorem Finset.card_pairs (s : Finset V) : #s.pairs = (#s).choose 2 := by sorry
