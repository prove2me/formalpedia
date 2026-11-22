-- Prove2me | Theorems.Thm_Auto_fromBlocks_diag_eq
-- name    : Auto.fromBlocks_diag_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:14.188374+00:00
-- url     : https://prove2.me/theorems/57449374-f831-4213-b335-fa25e9e573a0
-- title:
--   Auto: from Blocks diag eq
-- statement:
--   The Auto construction uses the from Blocks diag eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3451-L3455
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3451-L3455

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

theorem Auto.fromBlocks_diag_eq (X Y : Matrix ι ι ℂ) :
    Matrix.fromBlocks X 0 0 Y = (ein1 : Matrix (ι ⊕ ι) ι ℂ) * X * (ein1 : Matrix (ι ⊕ ι) ι ℂ)ᴴ +
      (ein2 : Matrix (ι ⊕ ι) ι ℂ) * Y * (ein2 : Matrix (ι ⊕ ι) ι ℂ)ᴴ := by sorry
