-- Prove2me | Theorems.Thm_Auto_tendsto_latticeFloor
-- name    : Auto.tendsto_latticeFloor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:08.952863+00:00
-- url     : https://prove2.me/theorems/810a8bbe-2df8-4581-b257-6f18ee83701e
-- title:
--   Auto: tendsto lattice Floor
-- statement:
--   The Auto construction uses the tendsto lattice Floor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L438-L450
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L438-L450

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

theorem Auto.tendsto_latticeFloor (x : Fin d → ℝ) :
    Tendsto (fun N : ℕ => latticeFloor N x) atTop (𝓝 x) := by sorry
