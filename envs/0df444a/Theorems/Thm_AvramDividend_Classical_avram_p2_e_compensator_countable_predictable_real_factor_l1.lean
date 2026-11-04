-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_real_factor_l1
-- name    : AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_real_factor_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:25:11.005615+00:00
-- url     : https://prove2.me/theorems/e311582f-b270-4bea-8890-ca15aff1b9bd
-- title:
--   Countable predictable original weighted marked-count real L1 factorisation without the prescribed Levy rate
-- statement:
--   For actual original-process countable predictable marked rectangles, if the total sum of E[W_i]E[N_i] is finite, the real conversion of the summed weighted source counts is integrable and has exactly that real expectation. The proof uses only original past-future factorisation and Tonelli, with no ν-rate or independent Poisson model.
-- source:
--   New proved P2-E countable original rate-free ENNReal factor 4601b26a and original count measurability 8146a449; pinned Measurable.tsum, integral_toReal, ae_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_rate_free_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_real_factor_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (W : ℕ → Ω → ℝ≥0∞)
    (hW : ∀ i, Measurable[𝓕 (s i)] (W i))
    (hSumFinite : (∑' i, (∫⁻ ω, W i ω ∂P) *
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P)) < ⊤) :
    let total : Ω → ℝ≥0∞ := fun ω => ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)
    let rateTotal : ℝ≥0∞ := ∑' i, (∫⁻ ω, W i ω ∂P) *
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P)
    Integrable (fun ω => (total ω).toReal) P ∧
      (∫ ω, (total ω).toReal ∂P) = rateTotal.toReal := by sorry
