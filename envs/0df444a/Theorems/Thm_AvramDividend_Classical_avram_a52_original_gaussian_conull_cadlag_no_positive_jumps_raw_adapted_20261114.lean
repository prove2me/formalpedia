-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a52_original_gaussian_conull_cadlag_no_positive_jumps_raw_adapted_20261114
-- name    : AvramDividend.Classical.avram_a52_original_gaussian_conull_cadlag_no_positive_jumps_raw_adapted_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:02:24.15083+00:00
-- url     : https://prove2.me/theorems/3c326db1-8883-4aa2-9ed4-099c609a8cf3
-- title:
--   Original Gaussian raw-adapted zero-start source has simultaneous conull cadlag paths without positive jumps
-- statement:
--   On the original probability space and raw filtration, the intrinsic Gaussian cutoff source admits an adapted, zero-start modification whose whole path is càdlàg with no positive jumps simultaneously on one probability-one event. The theorem explicitly retains the conull qualification.
-- source:
--   Proved A39 original raw adapted source continuous-path modification and A51 continuous-path left-limit lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian representative has the complete cadlag and no-upward-jump properties simultaneously on a single conull event. -/

theorem AvramDividend.Classical.avram_a52_original_gaussian_conull_cadlag_no_positive_jumps_raw_adapted_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P,
        (∀ t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
        (∀ t, 0 < t → ∃ l,
          Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
        (∀ t l, 0 < t →
          Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
          G t ω ≤ l)) := by sorry
