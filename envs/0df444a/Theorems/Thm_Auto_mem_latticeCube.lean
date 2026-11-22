-- Prove2me | Theorems.Thm_Auto_mem_latticeCube
-- name    : Auto.mem_latticeCube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:48.332801+00:00
-- url     : https://prove2.me/theorems/7f95ff65-deb4-4917-ac06-db134e7334ab
-- title:
--   Auto: mem lattice Cube
-- statement:
--   The Auto construction uses the mem lattice Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L410-L416
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L410-L416

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

theorem Auto.mem_latticeCube {N : ℕ} (hN : 0 < N) {k : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ latticeCube N k ↔ ∀ i, ⌊(N : ℝ) * x i⌋ = k i := by sorry
