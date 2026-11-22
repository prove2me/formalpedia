-- Prove2me | Theorems.Thm_Auto_hsRe_neg_right
-- name    : Auto.hsRe_neg_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:08.921813+00:00
-- url     : https://prove2.me/theorems/bef32095-4797-45db-8175-d1dc4c2847e4
-- title:
--   Auto: hs Re neg right
-- statement:
--   The Auto construction uses the hs Re neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L621-L623
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L621-L623

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
variable {m n : Type*} [Fintype m] [Fintype n]

theorem Auto.hsRe_neg_right (X Y : Matrix m n ℂ) :
    hsRe X (-Y) = - hsRe X Y := by sorry
