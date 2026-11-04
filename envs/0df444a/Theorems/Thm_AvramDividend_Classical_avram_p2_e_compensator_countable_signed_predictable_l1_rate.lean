-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_signed_predictable_l1_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_countable_signed_predictable_l1_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:14:38.692911+00:00
-- url     : https://prove2.me/theorems/a9abe5dd-4230-4838-b660-e7bfd1d94fc8
-- title:
--   Countable signed predictable original intrinsic marked integrands have real L1 and prescribed signed mean
-- statement:
--   For the actual original spectrally negative Lévy jump measure, a countable signed predictable rectangle integrand is the difference of nonnegative past-weighted jump-count sums. If both prescribed positive and negative ENNReal total rates are finite, the resulting signed real random variable is integrable and its expectation equals the difference of those real total rates. All source unconditional ν-rates remain explicit hypotheses; no independent Poisson model or martingale theorem is used.
-- source:
--   Accepted original count measurability 8146a449 and countable original weighted ν-rate 9d79c515; pinned Measurable.tsum, integral_toReal, ae_lt_top, and integral_sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_weighted_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_countable_signed_predictable_l1_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (Wpos Wneg : ℕ → Ω → ℝ≥0∞)
    (hWp : ∀ i, Measurable[𝓕 (s i)] (Wpos i))
    (hWn : ∀ i, Measurable[𝓕 (s i)] (Wneg i))
    (hRate : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) = (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)))
    (hSumPos : (∑' i, (∫⁻ ω, Wpos i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) < ⊤)
    (hSumNeg : (∑' i, (∫⁻ ω, Wneg i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) < ⊤) :
    let pos : Ω → ℝ≥0∞ := fun ω => ∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)
    let neg : Ω → ℝ≥0∞ := fun ω => ∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)
    let rp : ℝ≥0∞ := ∑' i, (∫⁻ ω, Wpos i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    let rn : ℝ≥0∞ := ∑' i, (∫⁻ ω, Wneg i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    Integrable (fun ω => (pos ω).toReal - (neg ω).toReal) P ∧
      (∫ ω, (pos ω).toReal - (neg ω).toReal ∂P) = rp.toReal - rn.toReal := by sorry
