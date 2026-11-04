-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_nu_count_real_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:16:37.314086+00:00
-- url     : https://prove2.me/theorems/14c106db-7c48-4e8b-a67e-60df9c72f117
-- title:
--   Original finite-rate marked jump count has the prescribed real first moment
-- statement:
--   For the actual spectrally negative Lévy process, finite original Lévy mark intensity and the independently established unconditional ENNReal source jump-rate identity imply that the Bochner real expectation of the literal marked count equals the real-valued rate. This converts the nonnegative first-moment compensator into the real L¹ framework required for signed compensated jump martingales, without assuming an independent Poisson measure or the canonical predictable compensator theorem.
-- source:
--   Proved P2-E count measurability 8146a449, pinned Mathlib ae_lt_top, integral_toReal and ENNReal.mul_lt_top. Original ν-rate remains external P2-D Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_nu_count_real_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫ ω, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal := by sorry
