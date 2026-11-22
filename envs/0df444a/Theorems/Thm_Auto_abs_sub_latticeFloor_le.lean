-- Prove2me | Theorems.Thm_Auto_abs_sub_latticeFloor_le
-- name    : Auto.abs_sub_latticeFloor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:44.551419+00:00
-- url     : https://prove2.me/theorems/e24035d8-651a-4043-b33d-57cd2e83afed
-- title:
--   Auto: abs sub lattice Floor le
-- statement:
--   The Auto construction uses the abs sub lattice Floor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L427-L436
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L427-L436

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem Auto.abs_sub_latticeFloor_le {N : ℕ} (hN : 0 < N) (x : Fin d → ℝ) (i : Fin d) :
    |x i - latticeFloor N x i| ≤ (N : ℝ)⁻¹ := by sorry
