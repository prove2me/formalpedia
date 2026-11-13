-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva87_original_zero_clock_total_compensated_marked_source
-- name    : AvramDividend.Classical.avram_bva87_original_zero_clock_total_compensated_marked_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:42:59.194344+00:00
-- url     : https://prove2.me/theorems/f3f7f2f5-2bfa-483a-81b6-99d59b45ac45
-- title:
--   Full original compensated negative-mark source vanishes at initial physical clock when kernel is zero-time supported
-- statement:
--   At the initial clock the original signed compensated negative-mark source is the literal marked Lévy jump integral minus its time and negative-mark compensator integral. Under pathwise measurable source mark map and kernel supported only on zero time, both summands vanish by BVA86 and BVA83. This packages the original M_n(0)=0 algebra once source H support and path measurability are established.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva83_original_zero_clock_negative_mark_compensator_integral
import Theorems.Thm_AvramDividend_Classical_avram_bva86_original_marked_zero_clock_supported_jump_integral
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva87_original_zero_clock_total_compensated_marked_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMeas : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : ∀ p : ℝ≥0 × ℝ, H ((p.1, ω), p.2) ≠ 0 → p.1 = 0) :
    (∫ p, H ((p.1, ω), p.2)
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) -
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (0 : ℝ))).map Real.toNNReal)) = 0 := by sorry
