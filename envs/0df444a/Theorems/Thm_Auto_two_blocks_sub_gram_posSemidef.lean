-- Prove2me | Theorems.Thm_Auto_two_blocks_sub_gram_posSemidef
-- name    : Auto.two_blocks_sub_gram_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:52.083837+00:00
-- url     : https://prove2.me/theorems/fdf0bf01-90af-48e5-912d-bb4abee6da95
-- title:
--   Auto: two blocks sub gram pos Semidef
-- statement:
--   The Auto construction uses the two blocks sub gram pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3583-L3596
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3583-L3596

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

theorem Auto.two_blocks_sub_gram_posSemidef (A V : Matrix ι ι ℂ) {η : ℝ} (hη : 0 ≤ η) :
    (((2 : ℝ) : ℂ) • Matrix.fromBlocks (Aᴴ * A + (η : ℂ) • 1) 0 0 (V * Vᴴ + (η : ℂ) • 1) -
      ((rowMat A V)ᴴ * rowMat A V + (η : ℂ) • 1)).PosSemidef := by sorry
