-- Prove2me | Theorems.Thm_Finset_lopsided_of_dependsOnCoords
-- name    : Finset.lopsided_of_dependsOnCoords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:23.548965+00:00
-- url     : https://prove2.me/theorems/7eb56c96-ea2f-4d57-a505-3f005c15333c
-- title:
--   Finset: lopsided of depends On Coords
-- statement:
--   **Independence gives the lopsided hypothesis.** If each `E i` depends only on the coordinates
--   `T i ⊆ U`, the hypothesis holds (with equality) for `Γ i` the indices `j ≠ i` with `T j` meeting
--   `T i`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L349-L362
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L349-L362

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
variable {E}
variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]

theorem Finset.lopsided_of_dependsOnCoords [DecidableEq ι] {I : Finset ι} {T : ι → Finset α}
    (hT : ∀ i ∈ I, T i ⊆ U)
    (hE : ∀ i ∈ I, DependsOnCoords (E i) (T i)) :
    Lopsided U p I E fun i => I.filter fun j => j ≠ i ∧ ¬Disjoint (T i) (T j) := by sorry
