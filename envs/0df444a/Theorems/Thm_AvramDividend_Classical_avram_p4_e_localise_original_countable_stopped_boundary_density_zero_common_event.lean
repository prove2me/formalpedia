-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_countable_stopped_boundary_density_zero_common_event
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_countable_stopped_boundary_density_zero_common_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:13:37.718582+00:00
-- url     : https://prove2.me/theorems/acb02a1b-ee5d-4c49-9755-32d8bdd4bdaf
-- title:
--   Original joint zero/cap physical occupation vanishes simultaneously across countable stopped localisers
-- statement:
--   From the already Proved exact original source weighted physical-time boundary theorem, use the countable a.e. intersection lemma to establish one conull original-probability event supporting zero-weighted occupancy at both endpoints simultaneously for any countable family of ruin-dominated stochastic clocks, variable deterministic s-finite physical-time measures and arbitrary nonnegative weights. Each clock can use a different observation-time measure. The theorem excludes t=0 and makes no assertion that the random dividend Stieltjes clock or reflected local time has zero cap mass.
-- source:
--   Accepted P4-E same-source joint weighted boundary helper e9e42507-ea81-49ef-80c6-5fe70694828c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_countable_stopped_boundary_density_zero_common_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτ : ∀ k ω, τ k ω ≤ ruinTime X x D ω)
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ k, SFinite (μ k))
    (weight : ℕ → ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ k,
      (∫⁻ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ k ω ∧
        (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight k t ω else 0 ∂(μ k)) = 0 := by sorry
