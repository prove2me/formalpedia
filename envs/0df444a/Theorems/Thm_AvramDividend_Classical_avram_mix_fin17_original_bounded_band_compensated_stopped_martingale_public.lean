-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
-- name    : AvramDividend.Classical.avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:34:22.370206+00:00
-- url     : https://prove2.me/theorems/61f39bfe-c919-48fb-a9da-ad7c879a256b
-- title:
--   Original finite-activity bounded-small-mark compensated martingale through a bounded stopping time
-- statement:
--   For the original finite-activity source, the compensated sum of negative marks in (-1,0) exists as the limit of source-exact small-band truncations. The bounded-mark field is an L1 martingale in the original right-continuous filtration and remains initially conditionally centred at any bounded original stopping time. Large negative marks are intentionally excluded because finite intensity permits infinite negative first moments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => Jsmall (τ ω) ω) ω = 0) := by sorry
