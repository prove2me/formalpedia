-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:51:53.340794+00:00
-- url     : https://prove2.me/theorems/51ec0583-746d-46ed-9584-8dd54835c9e0
-- title:
--   Original exact ruin-min-n clock discounted source exponential is L1 for any real q
-- statement:
--   The true original spectrally negative Lévy source exponential at the canonical finite ruin-truncated clock has an integrable q-discounted moment for every q and θ≥0, with no ψθ≤q constraint. Derive τ≤n from accepted source clock bounds and reuse the accepted genuine right-continuous bounded-stop L1 theorem.
-- source:
--   Proved source NNReal clock bound 6b7a13a0 and accepted original source unrestricted-q stopped exponential L1 b91875a4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) :
    Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by sorry
