-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_nat_count_realisation
-- name    : AvramDividend.Classical.avram_a20_original_negative_borel_nat_count_realisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:06:15.550778+00:00
-- url     : https://prove2.me/theorems/84a4791e-3ba0-42d5-8a8c-d87266348761
-- title:
--   Measurable natural-valued original negative-Borel physical jump count realisation
-- statement:
--   On the original spectrally negative Lévy probability space with finite total strictly negative jump intensity, the original marked negative-Borel count is almost surely finite and a measurable natural-valued random variable represents it exactly as a real count. Obtain the measurable natural count by rounding down the literal measured intrinsic real jump count. The genuine count measure is the ENat cardinal of original jump times, finite a.e. by the physical ν-intensity theorem; therefore the rounded value equals the actual jump count a.e. This is a source-level prerequisite to identifying its Poisson law without changing probability spaces.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Nat
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_negative_borel_nat_count_realisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    ∃ K : Ω → ℕ,
      Measurable K ∧
      ∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal := by sorry
