-- Prove2me | Theorems.Thm_Auto_exists_fin_shift
-- name    : Auto.exists_fin_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:56.730346+00:00
-- url     : https://prove2.me/theorems/6c8087f5-9f94-4eb1-9e40-fbf2ecea161b
-- title:
--   Auto: exists fin shift
-- statement:
--   The Auto construction uses the exists fin shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7424-L7430
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7424-L7430

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.exists_fin_shift {R : ℕ} {w : ℤ} (h : |w| ≤ R) :
    ∃ i : Fin (2 * R + 1), (i : ℤ) - R = w := by sorry
