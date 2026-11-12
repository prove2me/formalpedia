-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_mark_rate_left_continuous_on_cap
-- name    : AvramDividend.Classical.avram_bvb_b20_original_mark_rate_left_continuous_on_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:21:55.737628+00:00
-- url     : https://prove2.me/theorems/bba612af-3b3e-4240-bd6b-d82ea53ba698
-- title:
--   Original zero-jump mark-integrated compensation kernel is left-continuous on finite-cap contact domain
-- statement:
--   Under original finite-activity diffuse negative Lévy marks, the mark-integrated prepayment kernel composed with the original physical no-jump reserve is left-continuous from positive time on its closed-cap domain. No contact-occupation detection or grid sampling assumption is made.
-- source:
--   Actual original marked quadrature kernel continuity for Open phys95/912148aa, complementing boundary one-sided Fatou step.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_original_mark_rate_left_continuous_on_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
    let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ContinuousWithinAt
      (fun r : ℝ≥0 => ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
      (Ioc 0 t ∩ U ⁻¹' A) t := by sorry
