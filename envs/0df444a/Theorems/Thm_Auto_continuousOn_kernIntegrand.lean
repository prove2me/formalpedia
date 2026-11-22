-- Prove2me | Theorems.Thm_Auto_continuousOn_kernIntegrand
-- name    : Auto.continuousOn_kernIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:33.416949+00:00
-- url     : https://prove2.me/theorems/76eabd99-af7e-4484-89c0-250b40d00158
-- title:
--   Auto: continuous On kern Integrand
-- statement:
--   The Auto construction uses the continuous On kern Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7220-L7223
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7220-L7223

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

theorem Auto.continuousOn_kernIntegrand (m : ℕ) (t : ℝ) :
    ContinuousOn (fun s => kernIntegrand m s t) (Set.Ioi 0) := by sorry
