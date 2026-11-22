-- Prove2me | Theorems.Thm_Auto_sqrt_sub_posSemidef
-- name    : Auto.sqrt_sub_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:37.191898+00:00
-- url     : https://prove2.me/theorems/4ffe2702-57b7-4045-b908-e5bdd384d525
-- title:
--   Auto: sqrt sub pos Semidef
-- statement:
--   The Auto construction uses the sqrt sub pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1196-L1209
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1196-L1209

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

theorem Auto.sqrt_sub_posSemidef {Y : Matrix n n ℂ} {η : ℝ} (hη : 0 ≤ η)
    (hY : (Y - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (CFC.sqrt Y - ((√η : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by sorry
