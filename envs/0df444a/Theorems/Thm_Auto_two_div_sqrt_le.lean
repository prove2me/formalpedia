-- Prove2me | Theorems.Thm_Auto_two_div_sqrt_le
-- name    : Auto.two_div_sqrt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:40.875982+00:00
-- url     : https://prove2.me/theorems/1cbc1257-918d-4e0f-b3e8-88c941b32bed
-- title:
--   Auto: two div sqrt le
-- statement:
--   The Auto construction uses the two div sqrt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5412-L5417
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5412-L5417

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

theorem Auto.two_div_sqrt_le : 2 * (√(2 * π))⁻¹ ≤ √(2 / π) := by sorry
