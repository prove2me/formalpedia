-- Prove2me | Theorems.Thm_Auto_dexp_sum
-- name    : Auto.dexp_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:57.0288+00:00
-- url     : https://prove2.me/theorems/7be9726e-e5e1-43e3-a256-00ec205202ca
-- title:
--   Auto: dexp sum
-- statement:
--   The Auto construction uses the dexp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6354-L6356
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6354-L6356

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section

theorem Auto.dexp_sum {m : ℕ} (hm : m = 3 ∨ m = 4) :
    dexp m 2 + dexp m 1 + dexp m 0 = m := by sorry
