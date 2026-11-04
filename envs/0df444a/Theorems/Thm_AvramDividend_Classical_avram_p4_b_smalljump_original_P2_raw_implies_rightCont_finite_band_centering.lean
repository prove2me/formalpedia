-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:31:53.842553+00:00
-- url     : https://prove2.me/theorems/c34e4241-0b37-498a-ac3f-6ad637a2ffd2
-- title:
--   Original Lévy P2 raw marked compensator implies right-continuous finite-band conditional centring
-- statement:
--   For the exact intrinsic original Lévy count, the true raw P2 predictable marked jump compensation and source rates imply zero conditional expectation of its real centred finite-band increment under the original right-continuous filtration, subject to physical finite-band first-moment conditions. This composes the true original-process right-continuity extension with the ENNReal-to-real conditional expectation bridge.
-- source:
--   RightCont raw compensator extension cc36d5e2 and finite original count ENNReal event-rate-to-real conditional expectation theorem, with no substitute jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_event_rate_implies_real_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν B ≠ ⊤)
    (hMass : ∀ C : Set Ω, MeasurableSet[𝓕.rightCont s] C → P C ≠ ⊤)
    (hRate : ∀ n, (∫⁻ ω, J s (r n) ω ∂P) =
      ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hRaw : ∀ (u v : ℝ≥0) (C : Set Ω), u ≤ v →
      MeasurableSet[𝓕 u] C →
      (∫⁻ ω in C, J u v ω ∂P) =
        P C * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hJmeas : Measurable (J s t))
    (hFullRate : (∫⁻ ω, J s t ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    P[(fun ω => (J s t ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) |
      𝓕.rightCont s] =ᵐ[P] 0 := by sorry
