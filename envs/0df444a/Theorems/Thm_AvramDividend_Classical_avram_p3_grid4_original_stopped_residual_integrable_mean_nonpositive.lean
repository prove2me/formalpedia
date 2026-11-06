-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_stopped_residual_integrable_mean_nonpositive
-- name    : AvramDividend.Classical.avram_p3_grid4_original_stopped_residual_integrable_mean_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:05:47.486207+00:00
-- url     : https://prove2.me/theorems/6e417370-9cb1-4470-bd67-1f85dd8f247d
-- title:
--   Integrable original BV stopped physical-grid residual has nonpositive mean
-- statement:
--   This original-source lemma integrates the already Proved physical-grid sign d5058688: on the actual Lévy X, ruin-clamped physical grid, and any nonnegative predictable candidate weights W, the exact finite BV negative-jump/drift residual is nonpositive almost surely. Assuming that very residual is L1, its expectation is therefore nonpositive. This is a genuine original-process drift budget, useful for constructing B_n in the canonical source certificate. Integrability remains an explicit required source hypothesis; the lemma does not imply the missing compensated jump/pathwise accounting identity.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_stopped_residual_integrable_mean_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) (hW : ∀ ω i, 0 ≤ W i ω) :
    let Z : Ω → ℝ := fun ω =>
        let u : ℕ → ℝ≥0 := fun i =>
          ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
        let τ : Ω → ℝ≥0 := fun ξ =>
          (min (ruinTime X x D ξ) (T : ℝ≥0∞)).toNNReal
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) -
            (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
              else 0)
        (∑ i ∈ Finset.range (m + 1),
          W i ω * (R (min (u i) (τ ω)) -
            R (min (u (i + 1)) (τ ω))))
    Integrable Z P → (∫ ω, Z ω ∂P) ≤ 0 := by sorry
