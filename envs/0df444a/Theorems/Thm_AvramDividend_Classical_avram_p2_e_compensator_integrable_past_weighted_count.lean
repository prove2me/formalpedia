-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_integrable_past_weighted_count
-- name    : AvramDividend.Classical.avram_p2_e_compensator_integrable_past_weighted_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:24:36.05853+00:00
-- url     : https://prove2.me/theorems/8ba383d2-aecf-4576-92b9-073e4bad420d
-- title:
--   Integrable past weights yield original finite-rate marked-count real-L¹ products
-- statement:
--   For the actual original Lévy process and any nonnegative F_s-measurable past weight with finite ENNReal expectation, a Borel mark band of finite Lévy ν mass has an integrable real product W·N_X((s,t]×B), assuming only the independent unconditional original ν-rate. This is the L¹ weighted-domain bridge for predictable simple stochastic-integral and martingale constructions, without assuming a compensator or Poisson replacement.
-- source:
--   P2-E Proved source count measurability 8146a449 and weighted rate conditional e13617a2; pinned Mathlib integrable_toReal_of_lintegral_ne_top and ENNReal.mul_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_integrable_past_weighted_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hWfinite : (∫⁻ ω, W ω ∂P) < ⊤)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Integrable (fun ω => (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P := by sorry
