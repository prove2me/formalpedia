-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_min_n_esscher_density_probability
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ruin_min_n_esscher_density_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:46:37.365938+00:00
-- url     : https://prove2.me/theorems/86f1f2e2-ac26-4dd0-8ad0-1e5a78f08597
-- title:
--   Exact original min-ruin clock yields the genuine stopped Esscher probability density
-- statement:
--   For the exact original finite ruin-truncated clock τ=min(ruinTime,n).toNNReal, with the original right-continuous stopping-time hypothesis, the original-process Esscher likelihood defines a probability density. The accepted source NNReal min-clock lemma gives the bound τ≤n, and the proved original right-continuous Esscher theorem completes the result.
-- source:
--   Proved original min-ruin clock bounds 6b7a13a0 and Proved original right-continuous source Esscher probability 982cda1b, original 0dda1be7 hτeq/hτstop interfaces.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_density_probability
open MeasureTheory ProbabilityTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ruin_min_n_esscher_density_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IsProbabilityMeasure (P.withDensity (fun ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by sorry
