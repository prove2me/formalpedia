-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_rightcont_arbitrary_horizon_bounded_stopped_source_local_finite
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_rightcont_arbitrary_horizon_bounded_stopped_source_local_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:58:18.057813+00:00
-- url     : https://prove2.me/theorems/78a39dfa-e79e-40af-8640-46ae7e0f1e15
-- title:
--   Original BV right-continuous source occupation is finite on every Borel mark band in arbitrary horizon-bounded stopping regions
-- statement:
--   For actual BV SpectrallyNegativeLevy X on its original right-continuous filtration, an arbitrary stopping/predictable region S contained in the finite physical horizon {clock≤T}, not just the deterministic horizon itself, has finite restricted original source occupation mass on every Borel mark band. Direct monotonicity from the canonically Proved original-source horizon hLocal. Does not assume or assert individual-band marked Lévy intensity.
-- source:
--   Canonical Proved original rightCont BV hLocal ef573ae0, transport unchanged K/M/P/X and monotonicity for S subset of physical horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_original_rightcont_horizon_stopped_source_local_finite_all_marks
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_rightcont_arbitrary_horizon_bounded_stopped_source_local_finite
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
    (hST : S ⊆ {p | p.1.1 ≤ T})
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) ≠ ⊤ := by sorry
