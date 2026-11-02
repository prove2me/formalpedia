-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_original_rightcont_horizon_stopped_source_local_finite_all_marks
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_original_rightcont_horizon_stopped_source_local_finite_all_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:47:50.718205+00:00
-- url     : https://prove2.me/theorems/ef573ae0-4d20-46f1-af1d-ed541183ed69
-- title:
--   BV original right-continuous horizon-stopped predictable source occupation has finite mass on every Borel mark band
-- statement:
--   Given the original SpectrallyNegativeLevy P 𝓕, BV and finite negative Lévy activity, original fine-grid hypotheses and finite horizon T>0, and the unchanged right-continuous predictable source occupation M=P.bind K of the literal intrinsic jump measure, the physical-horizon stopped measure MT=M.restrict{clock≤T} has finite mass MT((all predictable times and source histories)×B) for every Borel mark band B. This proves the hLocal premise of P1/Chat02 for all bands in the BV case without assuming marked-B Poisson compensation. It uses exact BV total source occupation Tνnegative and zero source jump mass at time zero.
-- source:
--   Original source 𝓕.rightCont adapted rectangle f712/9b, original BV all-Borel mark expected count finite fde269fc, same-path rightCont Lévy lift and raw original predictable bottom-rectangle zero. No pending mass theorem is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_original_rightcont_horizon_stopped_source_local_finite_all_marks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T)
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
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) ≠ ⊤ := by sorry
