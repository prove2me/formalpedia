-- Prove2me | Theorems.Thm_Finset_pairs_eq_image_offDiag
-- name    : Finset.pairs_eq_image_offDiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:00:48.679403+00:00
-- url     : https://prove2.me/theorems/c271ac71-7e3e-414a-9c73-2a5305ba8a3b
-- title:
--   Finset: pairs eq image off Diag
-- statement:
--   The pairs of distinct elements of `s` are the image of `s.offDiag` in `Sym2`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L77-L89
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L77-L89

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

theorem Finset.pairs_eq_image_offDiag (s : Finset V) : s.pairs = s.offDiag.image Sym2.mk.uncurry := by sorry
