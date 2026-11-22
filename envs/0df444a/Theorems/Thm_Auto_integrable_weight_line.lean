-- Prove2me | Theorems.Thm_Auto_integrable_weight_line
-- name    : Auto.integrable_weight_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:14.569829+00:00
-- url     : https://prove2.me/theorems/d5cb8e0f-edb4-4623-b855-1d83216c9419
-- title:
--   Auto: integrable weight line
-- statement:
--   The Auto construction uses the integrable weight line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5734-L5736
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5734-L5736

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.integrable_weight_line (u h σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun t => h * gaussian σ (u - t)) := by sorry
