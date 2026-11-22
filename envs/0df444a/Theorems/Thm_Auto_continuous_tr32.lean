-- Prove2me | Theorems.Thm_Auto_continuous_tr32
-- name    : Auto.continuous_tr32
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:19.678779+00:00
-- url     : https://prove2.me/theorems/a889bd2f-941d-4977-9e3a-0a807946ad53
-- title:
--   Auto: continuous tr32
-- statement:
--   The Auto construction uses the continuous tr32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4668-L4671
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4668-L4671

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Auto.continuous_tr32 {Γ K : X → Matrix κ κ ℂ} (hΓ : Continuous Γ) (hK : Continuous K)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => HeatData.tr32 η (Γ x) (K x) := by sorry
