-- Prove2me | Theorems.Thm_Auto_wGram_smul
-- name    : Auto.wGram_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:19.847927+00:00
-- url     : https://prove2.me/theorems/48bae868-d908-4b3e-984e-69adc52cbd2e
-- title:
--   Auto: w Gram smul
-- statement:
--   The Auto construction uses the w Gram smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2976-L2981
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2976-L2981

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
omit [DecidableEq κ] [Fintype κ]

theorem Auto.wGram_smul (B : Matrix ι κ ℂ) (c : ℝ) (f : ι → ℝ) :
    wGram B (c • f) = (c : ℂ) • wGram B f := by sorry
