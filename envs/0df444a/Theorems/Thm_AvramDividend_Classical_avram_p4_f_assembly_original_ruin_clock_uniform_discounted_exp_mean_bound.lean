-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_uniform_discounted_exp_mean_bound
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ruin_clock_uniform_discounted_exp_mean_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:51:21.141767+00:00
-- url     : https://prove2.me/theorems/727e5451-25b8-4850-bb6c-292e2a9a413b
-- title:
--   Exact original ruin-min-n clock quantitative exponential moment bound
-- statement:
--   At the canonical original finite ruin-truncated clock τ=(ruinTime∧n).toNNReal, the discounted source exponential expectation is bounded by exp(|ψθ−q| n), for θ≥0 and any real q. The clock bound τ≤n is extracted from the Proved original source clock identity, then the Proved uniform right-continuous source Esscher moment theorem applies.
-- source:
--   Proved exact min ruin-clock bound 6b7a13a0 and accepted original uniform source exponential moment 7bd787b2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ruin_clock_uniform_discounted_exp_mean_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤
      Real.exp (|X.ψ θ - q| * (n : ℝ)) := by sorry
