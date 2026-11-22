-- Prove2me | Theorems.Thm_Auto_sum_shift
-- name    : Auto.sum_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:23.817389+00:00
-- url     : https://prove2.me/theorems/7a1e3724-6987-4fd2-ad10-7a0b013c4691
-- title:
--   Auto: sum shift
-- statement:
--   Translating one center changes the center-plane sum by exactly the translation.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7069-L7073
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7069-L7073

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

theorem Auto.sum_shift (v : Fin 3) (q : Fin 2 → ℝ) (d : ℝ) :
    Function.update (planePt q) v (planePt q v + d) 0 +
      Function.update (planePt q) v (planePt q v + d) 1 +
      Function.update (planePt q) v (planePt q v + d) 2 = d := by sorry
