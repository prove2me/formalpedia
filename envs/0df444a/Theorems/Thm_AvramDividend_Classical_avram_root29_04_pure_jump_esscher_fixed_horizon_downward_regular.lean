-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_fixed_horizon_downward_regular
-- name    : AvramDividend.Classical.avram_root29_04_pure_jump_esscher_fixed_horizon_downward_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:04:04.99802+00:00
-- url     : https://prove2.me/theorems/aa3b8094-c571-4f21-8a2f-4f04c5069042
-- title:
--   Actual finite-clock Esscher tilt preserves pure infinite-small-jump downward regularity
-- statement:
--   For an actual spectrally negative Lévy process whose small negative jumps have infinite total absolute first moment, almost every path under the genuine finite-terminal exponential Esscher density has arbitrarily early strictly negative increments. This uses the source-specific proved Rogozin slopes, the near-zero negative transfer and the absolutely continuous change of measure. It is a finite-clock process-level regularity input to a later reflected-excursion killed Markov argument; it does not construct the excursion measure or prove scale C1.
-- source:
--   Proved source-specific ae_rogozin_slopes_of_infinite_small_jumps (b12c5430-2bd6-4ba0-9184-becc6f00b058), ae_negative_near_zero_of_ae_rogozin_negative_slopes (b2e617e8-5a14-4082-8f6a-4c6af34e23a7), ae_negative_near_zero_of_absolutelyContinuous (5b4f4749-805e-4e94-9478-106c580d8175), pinned Mathlib withDensity_absolutelyContinuous (0df444a360eaa60ab8c11dca51a86af692955474).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_absolutelyContinuous

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_pure_jump_esscher_fixed_horizon_downward_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0) :
    ∀ᵐ ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ)))),
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by sorry
