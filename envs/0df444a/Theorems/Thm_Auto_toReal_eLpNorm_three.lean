-- Prove2me | Theorems.Thm_Auto_toReal_eLpNorm_three
-- name    : Auto.toReal_eLpNorm_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:58.379256+00:00
-- url     : https://prove2.me/theorems/bdb7a5c6-b339-4900-8611-3d87eb300310
-- title:
--   Auto: to Real e Lp Norm three
-- statement:
--   The Auto construction uses the to Real e Lp Norm three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7660-L7664
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7660-L7664

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

theorem Auto.toReal_eLpNorm_three {F : ℝ × ℝ → ℂ} (hF : MemLp F 3) :
    (eLpNorm F 3).toReal = (∫ p, ‖F p‖ ^ 3) ^ (1 / 3 : ℝ) := by sorry
