-- Prove2me | Theorems.Thm_Auto_continuousOn_kernIntegrand_joint
-- name    : Auto.continuousOn_kernIntegrand_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:00.97203+00:00
-- url     : https://prove2.me/theorems/fb838081-e0da-44d1-8299-a610a786ef70
-- title:
--   Auto: continuous On kern Integrand joint
-- statement:
--   The Auto construction uses the continuous On kern Integrand joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6936-L6943
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6936-L6943

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

theorem Auto.continuousOn_kernIntegrand_joint (m : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => kernIntegrand m z.1 z.2) {z | 0 < z.1} := by sorry
