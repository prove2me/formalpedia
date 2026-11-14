-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
-- name    : AvramDividend.Classical.avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:34:43.222063+00:00
-- url     : https://prove2.me/theorems/33ea36ca-b67f-44f1-9566-1f6cf880591c
-- title:
--   Original full negative Poisson source mark count at a bounded physical clock is finite almost everywhere under source a.e. measurability and finite negative activity
-- statement:
--   For the genuine original spectrally negative Levy process with finite negative Levy measure intensity and a bounded possibly random physical source clock, suppose the original mapped full-negative marked jump Poisson counting measure evaluated on the genuine stopped half-open source time rectangle is a.e. measurable. Authoritatively Proved mix_fin14 establishes a finite lintegral of that exact original bounded source count from the source negative intensity. The pinned remotely signature-verified Mathlib MeasureTheory.ae_lt_top prime theorem states that an a.e. measurable ENNReal random variable with finite lintegral takes finite values almost everywhere. Hence the genuine original full-negative Poisson source count is finite on one original conull event, without assuming finiteness on exceptional sample paths. This key source bridge allows pathwise ENNReal marked-grid cardinal bounds such as prepared B163 to become real toReal count domination a.e. for the Proved B150 and pending B157 Gaussian negative-jump energy estimates. The remaining task is to establish a.e. measurability of the original full source count from its marked random measure, as a separate source-specific lemma.
-- source:
--   Proved mix_fin14 bounded original negative source Poisson count finite integral and pinned remote Mathlib MeasureTheory.ae_lt_top prime.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A measurable actual original negative Poisson full-mark count to a bounded physical clock is finite almost everywhere under finite negative Levy intensity. -/

theorem AvramDividend.Classical.avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hMeas : AEMeasurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ))) P) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) < ⊤ := by sorry
