-- Prove2me | Theorems.Thm_Auto_wGram_isHermitian
-- name    : Auto.wGram_isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:49.914339+00:00
-- url     : https://prove2.me/theorems/b5439ce0-4cbb-4e58-879a-43427c50a105
-- title:
--   Auto: w Gram is Hermitian
-- statement:
--   The Auto construction uses the w Gram is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2956-L2958
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2956-L2958

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

theorem Auto.wGram_isHermitian (B : Matrix ι κ ℂ) (f : ι → ℝ) : (wGram B f).IsHermitian := by sorry
