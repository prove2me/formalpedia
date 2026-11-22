-- Prove2me | Theorems.Thm_Auto_volume_coord_hyperplane
-- name    : Auto.volume_coord_hyperplane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:11.125146+00:00
-- url     : https://prove2.me/theorems/58b16e3f-6a88-404b-ad4e-20a760c2a74a
-- title:
--   Auto: volume coord hyperplane
-- statement:
--   The Auto construction uses the volume coord hyperplane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L452-L455
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L452-L455

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

theorem Auto.volume_coord_hyperplane (i : Fin d) (a : ℝ) : volume {x : Fin d → ℝ | x i = a} = 0 := by sorry
