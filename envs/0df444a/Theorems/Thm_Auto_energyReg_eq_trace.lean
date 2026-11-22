-- Prove2me | Theorems.Thm_Auto_energyReg_eq_trace
-- name    : Auto.energyReg_eq_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:44.944018+00:00
-- url     : https://prove2.me/theorems/885a7c33-618d-4e5f-95d4-fc13538557bc
-- title:
--   Auto: energy Reg eq trace
-- statement:
--   The Auto construction uses the energy Reg eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1354-L1403
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1354-L1403

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.energyReg_eq_trace {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    energyReg η P = (((P + (η : ℂ) • 1) * CFC.sqrt (P + (η : ℂ) • 1)).trace).re - η ^ (3 / 2 :
      ℝ) * Fintype.card n := by sorry
