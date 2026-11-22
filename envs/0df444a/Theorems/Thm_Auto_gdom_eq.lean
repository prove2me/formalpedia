-- Prove2me | Theorems.Thm_Auto_gdom_eq
-- name    : Auto.gdom_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:26.276421+00:00
-- url     : https://prove2.me/theorems/dbac7dd8-aaac-4529-8e4b-ef02720440c0
-- title:
--   Auto: gdom eq
-- statement:
--   The Auto construction uses the gdom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4741-L4743
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4741-L4743

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

theorem Auto.gdom_eq (ε : ℝ) (p : Fin 3 → ℝ) :
    gdom ε p = Real.exp (-ε * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2)) := by sorry
