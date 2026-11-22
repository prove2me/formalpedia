-- Prove2me | Theorems.Thm_Auto_continuous_Kern
-- name    : Auto.continuous_Kern
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:00.640185+00:00
-- url     : https://prove2.me/theorems/f71a7717-a3ac-4247-b6ac-38a54861b07d
-- title:
--   Auto: continuous Kern
-- statement:
--   The Auto construction uses the continuous Kern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6945-L6958
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6945-L6958

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
open Auto
noncomputable section

theorem Auto.continuous_Kern (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Continuous (Kern m a b) := by sorry
