-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_probability_iInter_limit
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_void_probability_iInter_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:39:19.163961+00:00
-- url     : https://prove2.me/theorems/a48efa08-558f-4b81-9ce7-26c686f4c224
-- title:
--   Original negative-band void probabilities converge to all-cutoff void probability under explicit measure hypotheses
-- statement:
--   For the genuine original negative-band void events E_k as cutoffs increase, if each E_k is null-measurable with respect to the exact original P and some E_k has finite measure, then the probability of the intersection over all cutoffs equals the infimum of the probabilities. This is a rigorous from-above probability limit, with all nontrivial measure hypotheses explicit.
-- source:
--   Conditional count-event limit for original Wave 7 Chat 06. Imports newly Proved source monotonicity 3b526dac-e40d-49e9-a571-d1130411adbd. It does not assert a source Poisson law, measurability of E_k, or L² martingale isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_and_levy_intensity_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_void_probability_iInter_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let E : ℕ → Set Ω := fun k =>
       {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) = 0}
     (∀ k, NullMeasurableSet (E k) P) →
     (∃ k, P (E k) ≠ ⊤) →
     P (⋂ k, E k) = ⨅ k, P (E k)) := by sorry
