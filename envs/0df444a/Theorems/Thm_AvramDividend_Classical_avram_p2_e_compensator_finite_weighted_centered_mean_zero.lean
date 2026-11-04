-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_weighted_centered_mean_zero
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_weighted_centered_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:36:47.854195+00:00
-- url     : https://prove2.me/theorems/160db679-eec1-4ce1-8079-44ffd4046133
-- title:
--   Centred original finite-rate predictable marked count has zero real mean
-- statement:
--   For the actual original Lévy jump count on (s,t] and a finite-rate Borel mark set, a nonnegative past F_s-measurable weight of finite expectation has an integrable compensated real weighted count. Its expectation is zero, conditional only on the separately established original unweighted ν-rate, using the proved source past factorisation and real mean conversion.
-- source:
--   P2-E original weighted real integrability and weighted first moment; Mathlib integral_sub and integrable_const. External general original rate remains separately Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_integrable_past_weighted_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_weighted_count_real_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_weighted_centered_mean_zero
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
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :
    Integrable (fun ω => (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      ((∫⁻ ω, W ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal) P ∧
    (∫ ω, (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      ((∫⁻ ω, W ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal ∂P) = 0 := by sorry
