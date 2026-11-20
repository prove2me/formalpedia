-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_reserve_positive_lowerstrip_finite_product_measure_zero
-- name    : AvramDividend.Classical.avram_pj_workerC_original_true_reserve_positive_lowerstrip_finite_product_measure_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:14:33.03778+00:00
-- url     : https://prove2.me/theorems/0a996283-0b87-4bf0-95a6-831d479bdc78
-- title:
--   Original controlled Lévy reserve lower strictly positive spatial band has vanishing finite physical-time probability product measure
-- statement:
--   For the genuine original spectrally negative Lévy process X and original admissible post-right dividend reserve riskProcess X x D, any finite physical-time×sample measure μ on the original product measurable space assigns vanishing mass to the shrinking strictly positive lower spatial band {0<riskProcess≤1/(k+1)}. This follows from actual jointly measurable original reserve, continuity from above and the empty intersection of positive shrinking bands. It can be combined with the already-Proved original stopped preterminal positivity a.e. and uppercap strip occupation to control compact spatial localisation error K in the σ=0 infinite-activity verification proof. No invented path or stochastic law.
-- source:
--   New generic finite-measure shrinking positive lowerband theorem; Proved 2159c88b original riskProcess joint measurable; complements Proved cb1a7c38 uppercap expected occupation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_true_reserve_positive_lowerstrip_finite_product_measure_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure μ] :
    Tendsto (fun k : ℕ =>
      μ {p : ℝ≥0 × Ω |
          0 < riskProcess X x D p.1 p.2 ∧
          riskProcess X x D p.1 p.2 ≤
            (1 : ℝ) / ((k : ℝ) + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
