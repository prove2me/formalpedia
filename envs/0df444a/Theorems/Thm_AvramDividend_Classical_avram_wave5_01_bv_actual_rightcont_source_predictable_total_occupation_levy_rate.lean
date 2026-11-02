-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_rightcont_source_predictable_total_occupation_levy_rate
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_rightcont_source_predictable_total_occupation_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:48:37.980825+00:00
-- url     : https://prove2.me/theorems/bce6319a-ef6f-4c08-b9bf-a23c066294c9
-- title:
--   Original BV right-continuous predictable full-mark occupation has exact finite source Lévy rate
-- statement:
--   For unchanged actual SpectrallyNegativeLevy P 𝓕 with bounded variation, finite Lévy intensity and source fine-grid hypotheses, the right-continuous original predictable occupation measure M=P.bind K of the actual same-path intrinsic jump measure has exact mass T ν((−∞,0)) on ((0,T]×Ω)×ℝ. The kernel K is pointwise identical to the original lifted source count and its measurability is discharged from the proved source rightCont kernel theorem. The proof converts the entire literal original count lintegral, and can discharge BV horizon localisation; it does not claim arbitrary negative mark compensation.
-- source:
--   Proved raw source f712115e adapted rectangle applied to the original exact-path rightCont Lévy lift Y.X=X.X and Proved original literal BV total expected count d8534d75. No unpublished import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_adapted_rectangle_eq_intrinsic_count_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_rightcont_source_predictable_total_occupation_levy_rate
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
    (hM : M = P.bind K) :
    M (((Ioc 0 T) ×ˢ (Set.univ : Set Ω)) ×ˢ (Set.univ : Set ℝ)) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
