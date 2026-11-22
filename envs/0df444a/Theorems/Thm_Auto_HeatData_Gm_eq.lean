-- Prove2me | Theorems.Thm_Auto_HeatData_Gm_eq
-- name    : Auto.HeatData.Gm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:55.628924+00:00
-- url     : https://prove2.me/theorems/e365e119-b59b-495e-a556-8937ccd717a5
-- title:
--   Heat Data: Gm eq
-- statement:
--   The Heat Data construction uses the Gm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5870-L5872
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5870-L5872

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)

theorem Auto.HeatData.Gm_eq (β s : ℝ) (p : Fin 3 → ℝ) :
    Gm β 0 s p = gaussian (β * s) (p 0 + p 1 + p 2) := by sorry
