-- Prove2me | Theorems.Thm_Auto_re_diag_le_of_sub_posSemidef
-- name    : Auto.re_diag_le_of_sub_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:42.744316+00:00
-- url     : https://prove2.me/theorems/d4bb119b-5de7-4461-b1fd-c3d840cb17df
-- title:
--   Auto: re diag le of sub pos Semidef
-- statement:
--   The Auto construction uses the re diag le of sub pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1601-L1607
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1601-L1607

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n]

theorem Auto.re_diag_le_of_sub_posSemidef {A B : Matrix n n ℂ} (hAB : (B - A).PosSemidef) (i : n) :
    (A i i).re ≤ (B i i).re := by sorry
