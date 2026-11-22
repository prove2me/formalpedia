-- Prove2me | Theorems.Thm_Auto_constD_spec
-- name    : Auto.constD_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:53.954792+00:00
-- url     : https://prove2.me/theorems/84b2f9df-1c74-425c-974f-88a74c2bc1bf
-- title:
--   Auto: const D spec
-- statement:
--   The Auto construction uses the const D spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6870-L6877
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6870-L6877

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

theorem Auto.constD_spec :
    0 ≤ constD ∧ ∀ (m : ℕ) (v : Fin 3) (s : ℝ), 0 < s → ∀ x, |Dfun (dexp m v) s x| ≤ constD := by sorry
