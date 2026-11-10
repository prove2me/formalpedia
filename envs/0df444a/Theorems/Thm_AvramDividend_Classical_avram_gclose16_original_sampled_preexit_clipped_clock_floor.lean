-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_sampled_preexit_clipped_clock_floor
-- name    : AvramDividend.Classical.avram_gclose16_original_sampled_preexit_clipped_clock_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:29:45.635206+00:00
-- url     : https://prove2.me/theorems/e129ae1d-f491-45ec-a7b1-d2cae42adc66
-- title:
--   Original sampled lower-exit clipped stopping clock preserves a strict prior reserve floor
-- statement:
--   For an original spectrally negative controlled reserve, clip any original right-continuous filtration stopping time at its dense sampled lower reserve exit. The clipped time remains a genuine right-continuous filtration stopping time, lies below the original clock, and ensures the postpayment reserve stays above the threshold at every strictly earlier physical time. This is the exact stopping-clock and pre-exit floor primitive needed by finite-cap Gaussian localisation; separate clock cofinality and reward convergence remain necessary.
-- source:
--   Derive right-continuous stopping from Proved sampled lower-exit stopping 01e18751 and the Mathlib min theorem, then apply Proved dense-grid preexit floor 96609baa using the minimum clock order. No additional Ito/Fatou hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_sampled_lower_exit_stopping
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_dense_lower_preexit_floor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose16_original_sampled_preexit_clipped_clock_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → WithTop ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont σ)
    (r : ℕ → ℝ≥0)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (δ : ℝ) :
    let E : Ω → WithTop ℝ≥0 := fun ω =>
      ⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤
    let ρ : Ω → WithTop ℝ≥0 := fun ω => min (σ ω) (E ω)
    IsStoppingTime 𝓕.rightCont ρ ∧
      (∀ ω, ρ ω ≤ σ ω) ∧
      ∀ (ω : Ω) (T : ℝ≥0), (T : WithTop ℝ≥0) ≤ ρ ω →
        ∀ s : ℝ≥0, s < T →
          δ ≤ x + X.X s ω - rightLimit D s ω := by sorry
