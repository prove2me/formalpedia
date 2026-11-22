-- Prove2me | Theorems.Thm_Auto_heatTrace_bound
-- name    : Auto.heatTrace_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:54:35.621969+00:00
-- url     : https://prove2.me/theorems/67c44504-b86f-4371-8278-592824606f9a
-- title:
--   Auto: heat Trace bound
-- statement:
--   Source `tau`: the center-integrated trace is controlled by the three energy densities.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7116-L7218
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7116-L7218

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.heatTrace_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {s : ℝ} (hs : 0 < s) :
    ‖((1 / s : ℝ) : ℂ) * ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ ≤
      ENNReal.ofReal (5 / 3 * constD * constA ^ 2) *
        ∑ v, ∫⁻ p, heatCost Hd (rateAt v) (s, p) := by sorry
