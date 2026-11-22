-- Prove2me | Theorems.Thm_Auto_wGram_apply
-- name    : Auto.wGram_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:14.537964+00:00
-- url     : https://prove2.me/theorems/b7c43fdf-52a5-4505-961b-6cba7f8e748a
-- title:
--   Auto: w Gram apply
-- statement:
--   The Auto construction uses the w Gram apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2961-L2964
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2961-L2964

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

theorem Auto.wGram_apply (B : Matrix ι κ ℂ) (f : ι → ℝ) (a b : κ) :
    wGram B f a b = ∑ i, star (B i a) * (f i : ℂ) * B i b := by sorry
