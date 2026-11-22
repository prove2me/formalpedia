-- Prove2me | Theorems.Thm_Auto_constA_spec
-- name    : Auto.constA_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:12.812981+00:00
-- url     : https://prove2.me/theorems/c10e7496-b7eb-4ab6-aee0-b8bda5450d3b
-- title:
--   Auto: const A spec
-- statement:
--   The Auto construction uses the const A spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6879-L6888
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6879-L6888

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

theorem Auto.constA_spec :
    0 ≤ constA ∧ ∀ (m : ℕ) (v : Fin 3) (s : ℝ), 0 < s → ∀ d, |acoef (dexp m v) s d| ≤ constA *
      √s := by sorry
