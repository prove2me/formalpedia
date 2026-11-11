-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite68_original_real_time_cap_contact_null
-- name    : AvramDividend.Classical.avram_gfinite68_original_real_time_cap_contact_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:07:53.824218+00:00
-- url     : https://prove2.me/theorems/7af019fa-e405-491c-aae6-142ee4d645a7
-- title:
--   Original stopped reserve has zero real Lebesgue time at finite cap
-- statement:
--   Transports authoritative original sigma-finite NNReal-time cap occupation to actual real Lebesgue times on a stopped original risk process, before ruin and within finite horizon. This is the stochastic cap-contact null-set step, independent of cutoffs or dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite68_original_real_time_cap_contact_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D s ω ≤ c)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          c ≤ riskProcess X x D (Real.toNNReal t) ω} = 0 := by
  sorry
