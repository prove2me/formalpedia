-- Prove2me | Theorems.Thm_Finset_avoids_insert
-- name    : Finset.avoids_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:09.372692+00:00
-- url     : https://prove2.me/theorems/c90d429e-8e2b-4e23-8a8e-fbc0b86aa2a9
-- title:
--   Finset: avoids insert
-- statement:
--   Avoiding `insert i S` is avoiding `E i` and avoiding `S`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L138-L140
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L138-L140

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
omit [∀ i, DecidablePred (E i)]

theorem Finset.avoids_insert [DecidableEq ι] {i : ι} {S : Finset ι} {a : β} :
    Avoids E (insert i S) a ↔ ¬E i a ∧ Avoids E S a := by sorry
