-- Prove2me | Theorems.Thm_Auto_rdiag_isHermitian
-- name    : Auto.rdiag_isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:06.564666+00:00
-- url     : https://prove2.me/theorems/f47ce342-f10a-41f8-ba94-b5115e8d87aa
-- title:
--   Auto: rdiag is Hermitian
-- statement:
--   The Auto construction uses the rdiag is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2939-L2941
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2939-L2941

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
omit [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem Auto.rdiag_isHermitian (f : ι → ℝ) :
    (rdiag f).IsHermitian := by sorry
