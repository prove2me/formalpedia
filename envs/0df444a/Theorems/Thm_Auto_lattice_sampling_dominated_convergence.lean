-- Prove2me | Theorems.Thm_Auto_lattice_sampling_dominated_convergence
-- name    : Auto.lattice_sampling_dominated_convergence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:51.336424+00:00
-- url     : https://prove2.me/theorems/24e2ca99-2d55-4170-b802-f8c29f9f8f0d
-- title:
--   Auto: lattice sampling dominated convergence
-- statement:
--   The Auto construction uses the lattice sampling dominated convergence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L457-L565
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L457-L565

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

theorem Auto.lattice_sampling_dominated_convergence (H : (Fin d → ℝ) → E) (hHb : ∃ M, ∀ x, ‖H x‖ ≤ M)
    (hHs : ∃ R, ∀ x, R < ‖x‖ → H x = 0) (S : Finset (Fin d × ℝ))
    (hHc : ∀ x, (∀ p ∈ S, x p.1 ≠ p.2) → ContinuousAt H x) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ d • ∑' k : Fin d → ℤ, H (fun i => (k i : ℝ) / N)) atTop
      (𝓝 (∫ x, H x)) := by sorry
