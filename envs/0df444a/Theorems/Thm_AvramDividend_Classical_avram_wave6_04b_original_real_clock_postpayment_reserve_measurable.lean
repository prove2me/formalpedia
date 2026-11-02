-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
-- name    : AvramDividend.Classical.avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:24:11.041891+00:00
-- url     : https://prove2.me/theorems/2d25282e-6220-4b0e-a0b1-8ba56b5fed07
-- title:
--   Actual post-payment Lévy reserve is measurable on real Stieltjes time
-- statement:
--   For every admissible dividend strategy and original spectrally negative Levy process, the actual path s↦x+X_(s.toNNReal)-D_(s.toNNReal)+ is Borel measurable as a function of real Stieltjes time. It follows from the source-specific càdlàg/adapted post-payment reserve and the measurable joint-evaluation theorem, and handles the real-to-NNReal time convention including time zero. This is a necessary input to make boundary-safe signed secant integrability automatic.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
--   import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- The original controlled post-payment reserve is Borel-measurable
--   as a real-clock path, including the negative-time toNNReal convention. -/
--   theorem AvramDividend.Classical.avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
--       (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
--       Measurable (fun s : ℝ =>
--         x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) := by
--     have hp := postPaymentReserve_cadlag_adapted X x D hD
--     let F : ℝ≥0 → Ω → ℝ := fun t ω =>
--       x + X.X t ω - rightLimit D t ω
--     have hsections (t : ℝ≥0) : Measurable (F t) := by
--       exact (hp.2.2 t).mono (𝓕.rightCont.le t) le_rfl
--     have hright : ∀ ω t, ContinuousWithinAt
--         (fun s : ℝ≥0 => F s ω) (Ici t) t := by
--       intro ω t
--       exact hp.1 ω t
--     have hjoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) :=
--       rightContinuous_measurable_sections_joint_evaluation F hsections hright
--     have hslice : Measurable (fun t : ℝ≥0 => F t ω) := by
--       exact hjoint.comp (measurable_id.prodMk measurable_const)
--     have hclock : Measurable (fun s : ℝ => s.toNNReal) :=
--       Real.toNNReal_mono.measurable
--     exact hslice.comp hclock

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    Measurable (fun s : ℝ =>
      x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) := by sorry
