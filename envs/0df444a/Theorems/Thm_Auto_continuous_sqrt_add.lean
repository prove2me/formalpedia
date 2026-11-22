-- Prove2me | Theorems.Thm_Auto_continuous_sqrt_add
-- name    : Auto.continuous_sqrt_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:47.714324+00:00
-- url     : https://prove2.me/theorems/cc6e37e7-406b-4c1c-b140-0408bce9a8c8
-- title:
--   Auto: continuous sqrt add
-- statement:
--   The Auto construction uses the continuous sqrt add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4661-L4666
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4661-L4666

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

theorem Auto.continuous_sqrt_add {Γ : X → Matrix κ κ ℂ} (hΓ : Continuous Γ)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => CFC.sqrt (Γ x + (η : ℂ) • 1) := by sorry
