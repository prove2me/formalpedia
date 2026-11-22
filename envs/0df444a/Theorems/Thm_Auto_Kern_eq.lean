-- Prove2me | Theorems.Thm_Auto_Kern_eq
-- name    : Auto.Kern_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:53.900785+00:00
-- url     : https://prove2.me/theorems/2d9b8105-9e0b-4ed7-9896-c0b11ae289cd
-- title:
--   Auto: Kern eq
-- statement:
--   The Auto construction uses the Kern eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6934-L6934
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6934-L6934

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

theorem Auto.Kern_eq (m : ℕ) (a b t : ℝ) : Kern m a b t = ∫ s in a..b, kernIntegrand m s t := by sorry
