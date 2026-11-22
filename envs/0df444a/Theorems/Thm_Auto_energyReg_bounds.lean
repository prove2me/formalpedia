-- Prove2me | Theorems.Thm_Auto_energyReg_bounds
-- name    : Auto.energyReg_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:25:45.923855+00:00
-- url     : https://prove2.me/theorems/e9a41191-53a6-47cd-bcc5-bc6bb52e4a4e
-- title:
--   Auto: energy Reg bounds
-- statement:
--   The Auto construction uses the energy Reg bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4407-L4425
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4407-L4425

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Auto.energyReg_bounds {P : Matrix κ κ ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ energyReg η P ∧ energyReg η P ≤ 2 * P.trace.re * √(P.trace.re + η) := by sorry
