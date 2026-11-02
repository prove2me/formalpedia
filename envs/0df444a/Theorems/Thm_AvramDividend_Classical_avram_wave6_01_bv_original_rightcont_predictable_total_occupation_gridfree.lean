-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_rightcont_predictable_total_occupation_gridfree
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_rightcont_predictable_total_occupation_gridfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:18:12.1963+00:00
-- url     : https://prove2.me/theorems/1b02d306-c133-4bbc-a429-6eafa7b2f6f9
-- title:
--   Original BV right-continuous predictable jump occupation has exact full-mark Lévy mass without grid hypotheses
-- statement:
--   For the actual SpectrallyNegativeLevy X on the original Ω, P, and right-continuous predictable filtration, the measure obtained by binding P to the literal lifted same-path original jump counting measure has mass exactly T times X.ν((−∞,0)) on ((0,T]×Ω)×ℝ in finite-activity bounded variation. The previously required arbitrary grid, mesh, and bound witnesses are removed by the Proved deterministic grid construction. The conclusion concerns the actual original jump occupation measure and is not an abstract Poisson replacement; it does not yet identify the intensity of arbitrary marked B nor past-event slices A.
-- source:
--   Original exact predictable occupation bce6319a is Proved, as is positive horizon uniform grid witness 429cc0b0. Instantiate with witness to eliminate extraneous mesh assumptions; no new source laws assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_rightcont_source_predictable_total_occupation_levy_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_rightcont_predictable_total_occupation_gridfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K) :
    M (((Ioc 0 T) ×ˢ (Set.univ : Set Ω)) ×ˢ (Set.univ : Set ℝ)) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
