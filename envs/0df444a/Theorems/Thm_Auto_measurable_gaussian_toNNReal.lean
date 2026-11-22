-- Prove2me | Theorems.Thm_Auto_measurable_gaussian_toNNReal
-- name    : Auto.measurable_gaussian_toNNReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:55.434029+00:00
-- url     : https://prove2.me/theorems/fcdc4192-4fdc-4b08-a3b2-7819b088faf9
-- title:
--   Auto: measurable gaussian to NNReal
-- statement:
--   The Auto construction uses the measurable gaussian to NNReal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6405-L6406
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6405-L6406

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

theorem Auto.measurable_gaussian_toNNReal (τ : ℝ) : Measurable fun d => (gaussian τ d).toNNReal := by sorry
