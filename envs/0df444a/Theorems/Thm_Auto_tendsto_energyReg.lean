-- Prove2me | Theorems.Thm_Auto_tendsto_energyReg
-- name    : Auto.tendsto_energyReg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:38.704805+00:00
-- url     : https://prove2.me/theorems/351ceaff-c47d-4317-8d27-c63e811238a2
-- title:
--   Auto: tendsto energy Reg
-- statement:
--   The Auto construction uses the tendsto energy Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5979-L5987
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5979-L5987

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.tendsto_energyReg {P : Matrix n n ℂ} (hP : P.IsHermitian) {η : ℕ → ℝ}
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => energyReg (η m) P) atTop (𝓝 (energyReg 0 P)) := by sorry
