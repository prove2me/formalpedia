-- Prove2me | Theorems.Thm_Auto_gweight_nonneg
-- name    : Auto.gweight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:37.629246+00:00
-- url     : https://prove2.me/theorems/5957874a-797e-4ab0-8668-9faac8cbd00a
-- title:
--   Auto: gweight nonneg
-- statement:
--   The Auto construction uses the gweight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2986-L2990
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2986-L2990

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι]

theorem Auto.gweight_nonneg (u : ι → ℝ) {h σ : ℝ} (hh : 0 ≤ h) (hσ : 0 < σ) (p : ℝ) (i : ι) :
    0 ≤ gweight u h σ p i := by sorry
