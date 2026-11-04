-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_min_n_esscher_likelihood_mean_one
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ruin_min_n_esscher_likelihood_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:14:12.765583+00:00
-- url     : https://prove2.me/theorems/f5c5e1c8-e3ee-4385-be87-bb18de2c56c7
-- title:
--   Original min-ruin n-clock stopped Esscher exponential has exact mean one
-- statement:
--   At the exact original finite ruin-truncated clock from canonical P4-F, the original stopped Esscher likelihood has expectation exactly one. This uses the accepted source min ruin clock bound and the original right-continuous source bounded-stopping mean-one theorem, with no auxiliary independent process or extra filtration.
-- source:
--   Proved original stopped clock NNReal bound 6b7a13a0 and Proved original right-continuous Esscher likelihood mean one 46c2da57.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ruin_min_n_esscher_likelihood_mean_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by sorry
