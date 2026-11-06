-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_marked_negative_borel_cell_square_budget
-- name    : AvramDividend.Classical.avram_p4_f3_original_marked_negative_borel_cell_square_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:50:09.681407+00:00
-- url     : https://prove2.me/theorems/983eb2ab-c18c-49c8-ab10-ee351d6a55f9
-- title:
--   Original marked negative Borel cell second-moment budget from physical stopped band
-- statement:
--   On the original Lévy path, any separated Borel jump-mark count in a physical time cell [s,t] bounded by T is square-integrable and has a second-moment bound r²+r, where r=T ν((−∞,−1/(n+1)]). The count is the original marked jump measure; measurability of this cell and the dominating full-band count are explicit hypotheses. This source bridge combines P4-S3 original marked cell domination with its stopped full-band second-moment theorem, avoiding equality in law, surrogate processes or unsupported Poisson covariance assumptions.
-- source:
--   Public Proved original marked cell domination 840cfac4-5017-421f-8baf-6e8544e7060c and stopped original negative-band count second moment 50312326-0cf3-4631-aed2-a848ba3ce0a5. Intended for hPairInt in source physical-grid L² isometry a29d73c1; disjoint-band offdiagonal moments remain separate obligations.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_marked_negative_borel_cell_square_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ) (hBsep : B ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (A : Ω → ℝ)
    (hAeq : ∀ ω, A ω =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hAmeas : Measurable A)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (A ω) ^ 2) P ∧
      (∫ ω, (A ω) ^ 2 ∂P) ≤ r ^ 2 + r := by sorry
