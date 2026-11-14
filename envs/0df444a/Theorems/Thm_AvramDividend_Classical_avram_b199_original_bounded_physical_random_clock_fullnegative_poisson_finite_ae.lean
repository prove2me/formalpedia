-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b199_original_bounded_physical_random_clock_fullnegative_poisson_finite_ae
-- name    : AvramDividend.Classical.avram_b199_original_bounded_physical_random_clock_fullnegative_poisson_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:47:32.505586+00:00
-- url     : https://prove2.me/theorems/737e7c23-db3b-43f9-be46-6a0d1e862780
-- title:
--   Genuine original full negative Poisson jump count up to any bounded measurable random physical clock is finite almost everywhere under finite negative activity
-- statement:
--   For the actual original spectrally negative Levy source with finite negative mark intensity and any bounded measurable possibly random physical stopping clock, the complete marked source Poisson count of all strictly negative jumps in the half-open source time interval before that clock is finite almost everywhere under the original probability measure. Prepared B198 derives measurability of this full source count from Proved original random-interval negative reciprocal cutoff count measurability and the pathwise monotone measure limit B197. Prepared B195 then applies the remotely signature-verified ae_lt_top prime theorem to the Proved mix_fin14 finite expected full original negative source count, delivering actual conull finiteness. The conclusion introduces no measurability premise, no all-path finite negative jump count assumption, and no source replacement. This is the exact a.e. finiteness needed to turn ENNReal original marked-grid source count domination into real toReal count domination safely for the Proved B150 and pending B157 Gaussian-negative stopped mesh energy estimates. Publish only once B198 and B195 Proved.
-- source:
--   Prepared B198 measurable full original negative Poisson source count and B195 conull finiteness from Proved original mix_fin14 finite expected source count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under finite original negative Levy activity, the complete genuine original marked Poisson count up to any bounded measurable random physical clock is finite almost surely. -/

theorem AvramDividend.Classical.avram_b199_original_bounded_physical_random_clock_fullnegative_poisson_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσ : Measurable σ)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) < ⊤ := by sorry
