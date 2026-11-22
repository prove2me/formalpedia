-- Prove2me | Theorems.Thm_Auto_hsRe_sub_right
-- name    : Auto.hsRe_sub_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:09.96006+00:00
-- url     : https://prove2.me/theorems/b5365973-ed25-42d2-bd8e-b3ecbfc4e48b
-- title:
--   Auto: hs Re sub right
-- statement:
--   The Auto construction uses the hs Re sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L625-L627
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L625-L627

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

theorem Auto.hsRe_sub_right (X Y Z : Matrix m n ℂ) :
    hsRe X (Y - Z) = hsRe X Y - hsRe X Z := by sorry
