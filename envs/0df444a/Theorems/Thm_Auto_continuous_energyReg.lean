-- Prove2me | Theorems.Thm_Auto_continuous_energyReg
-- name    : Auto.continuous_energyReg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:29.203971+00:00
-- url     : https://prove2.me/theorems/196dd129-12d8-4d87-8d8c-89c07d1c32ab
-- title:
--   Auto: continuous energy Reg
-- statement:
--   The Auto construction uses the continuous energy Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4673-L4682
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4673-L4682

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

theorem Auto.continuous_energyReg {Γ : X → Matrix κ κ ℂ} (hΓ : Continuous Γ)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => energyReg η (Γ x) := by sorry
