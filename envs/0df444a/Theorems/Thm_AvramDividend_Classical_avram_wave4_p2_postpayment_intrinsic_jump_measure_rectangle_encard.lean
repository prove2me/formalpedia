-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_jump_measure_rectangle_encard
-- name    : AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_jump_measure_rectangle_encard
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:06:22.88418+00:00
-- url     : https://prove2.me/theorems/4da1cc04-ee62-4daa-8318-c29854a5a4b3
-- title:
--   Full original controlled postpayment jump measure counts actual marked jumps in Borel rectangles
-- statement:
--   On each actual original sample of a spectrally negative Lévy source and any admissible dividend strategy, the full postpayment intrinsic marked jump measure on a Borel time-and-mark rectangle (s,t]×B equals the extended cardinality of exactly the positive-time nonzero combined jumps ΔX−(D_{t+}−D_t) within that rectangle. Simultaneous source and dividend atoms are accounted for; no independent Poisson surrogate, compensation, or finite-activity assumption is used.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), chronological source/payment marks (5.11)–(5.12). Existing canonically Proved postpayment measure equality 282556df and joint mark measurability 0c60d413; exact original Lévy rectangle analogue f6336d40 proves the measurable map, restrict and count pattern.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_jump_measure_rectangle_encard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)))
      (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
        (rightLimit D u ω - D u ω)) ≠ 0 ∧
      ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
        (rightLimit D u ω - D u ω)) ∈ B}).encard := by sorry
