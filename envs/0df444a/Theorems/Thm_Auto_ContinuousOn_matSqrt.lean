-- Prove2me | Theorems.Thm_Auto_ContinuousOn_matSqrt
-- name    : Auto.ContinuousOn.matSqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:02.490597+00:00
-- url     : https://prove2.me/theorems/dfc7396d-9cbd-4cc2-962e-2ff3c3d82373
-- title:
--   Continuous On: mat Sqrt
-- statement:
--   The Continuous On construction uses the mat Sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3944-L3955
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3944-L3955

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
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.ContinuousOn.matSqrt {Z : Type*} [TopologicalSpace Z] {f : Z → Matrix n n ℂ} {s : Set Z}
    (hf : ContinuousOn f s) {η : ℝ} (hη : 0 < η)
    (hpos : ∀ z ∈ s, (f z - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    ContinuousOn (fun z => CFC.sqrt (f z)) s := by sorry
