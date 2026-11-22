-- Prove2me | Theorems.Thm_Auto_continuous_rdiag
-- name    : Auto.continuous_rdiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:35:55.7628+00:00
-- url     : https://prove2.me/theorems/9110f3d7-4e68-4890-9410-aa47dc7a969d
-- title:
--   Auto: continuous rdiag
-- statement:
--   The Auto construction uses the continuous rdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4577-L4579
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4577-L4579

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
omit [Fintype ι]

theorem Auto.continuous_rdiag {f : X → ι → ℝ} (hf : ∀ i, Continuous fun x => f x i) :
    Continuous fun x => rdiag (f x) := by sorry
