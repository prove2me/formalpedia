-- Prove2me | Theorems.Thm_Auto_integrable_gdom
-- name    : Auto.integrable_gdom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:21.527988+00:00
-- url     : https://prove2.me/theorems/d864bfe8-08e9-4489-a7cf-7d8b0a7afcd3
-- title:
--   Auto: integrable gdom
-- statement:
--   The Auto construction uses the integrable gdom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4745-L4747
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4745-L4747

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
open Auto
noncomputable section

theorem Auto.integrable_gdom {ε : ℝ} (hε : 0 < ε) : Integrable (gdom ε) := by sorry
