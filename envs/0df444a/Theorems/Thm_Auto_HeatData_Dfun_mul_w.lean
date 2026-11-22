-- Prove2me | Theorems.Thm_Auto_HeatData_Dfun_mul_w
-- name    : Auto.HeatData.Dfun_mul_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:49.595413+00:00
-- url     : https://prove2.me/theorems/4ed28f11-ab4e-4470-905b-2beb2f312495
-- title:
--   Heat Data: Dfun mul w
-- statement:
--   The Heat Data construction uses the Dfun mul w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6719-L6727
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6719-L6727

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
omit [Fintype ι] [DecidableEq ι]

theorem Auto.HeatData.Dfun_mul_w (hh : 0 ≤ Hd.h) (d : ℕ) {s : ℝ} (hs : 0 < s) (p : Fin 3 → ℝ) (v : Fin 3)
    (i : ι) :
    Dfun d s (Hd.u i - p v) * Hd.sqw p (fun _ => 11 / 10 * s) v i ^ 2 = Hd.h * (√s ^ d *
      gaussianD d (21 / 20 * s) (Hd.u i - p v)) := by sorry
