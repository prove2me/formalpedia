-- Prove2me | Theorems.Thm_Auto_gaussian_anti
-- name    : Auto.gaussian_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:21.15911+00:00
-- url     : https://prove2.me/theorems/31d8c048-ca07-4c60-abfc-a32d68674174
-- title:
--   Auto: gaussian anti
-- statement:
--   The Auto construction uses the gaussian anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5397-L5402
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5397-L5402

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

theorem Auto.gaussian_anti {σ : ℝ} (hσ : 0 < σ) {t t' : ℝ} (h : |t| ≤ |t'|) :
    gaussian σ t' ≤ gaussian σ t := by sorry
