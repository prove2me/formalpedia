-- Prove2me | Theorems.Thm_Auto_ofReal_costTerm_le
-- name    : Auto.ofReal_costTerm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:05.157625+00:00
-- url     : https://prove2.me/theorems/f1140297-d2e4-418b-856f-f229d3b4415c
-- title:
--   Auto: of Real cost Term le
-- statement:
--   The Auto construction uses the of Real cost Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L872-L887
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L872-L887

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]

theorem Auto.ofReal_costTerm_le (k x : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal ((3 / 2) * (2 * ((starRingEnd ℂ) k * x).re - c * ‖x‖ ^ 2)) ≤ ENNReal.ofReal
      ((3 / 2) * ‖k‖ ^ 2) / ENNReal.ofReal c := by sorry
