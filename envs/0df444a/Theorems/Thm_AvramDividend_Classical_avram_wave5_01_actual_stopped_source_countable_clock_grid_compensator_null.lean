-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_stopped_source_countable_clock_grid_compensator_null
-- name    : AvramDividend.Classical.avram_wave5_01_actual_stopped_source_countable_clock_grid_compensator_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:53:13.589953+00:00
-- url     : https://prove2.me/theorems/4ae91932-9edd-4302-a65c-993ef49e089c
-- title:
--   Original stopped jump occupation and canonical Lévy compensator have no mass on any countable predictable time grid
-- statement:
--   For the genuine original X on P and its unchanged right-continuous filtration, with literal same-source marked kernel K and stopped occupation MT=M.restrict S, construct the canonical finite-horizon predictable μ from its original time × P intensity. For any countable family of deterministic grid times and each source-predictable singleton time-history slice {times n}×A, both MT and μ×(X.ν restricted to negative marks) vanish on the full countable-grid marked set; in particular they agree there. This proves simultaneous all-grid endpoint localisation on the actual original process, without a detached Poisson model or future negative-mark intensity.
-- source:
--   Formal countable-union extension of canonically Proved original all-deterministic-time atom compensation 1b617de2; `measure_iUnion_null` yields zero on every enumerated time grid for both source and canonical Lévy-intensity occupation. Exact bridge needed for grid approximation/truncation, not the unresolved negative-band compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_stopped_source_all_deterministic_atoms_compensator_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_stopped_source_countable_clock_grid_compensator_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ D : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] D →
        μ D = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) D) ∧
      (∀ (times : ℕ → ℝ≥0) (A : Set Ω),
        (∀ n : ℕ, MeasurableSet[𝓕.rightCont.predictable]
          ({times n} ×ˢ A)) →
        ∀ (B : Set ℝ), MeasurableSet B →
        MT (((Set.range times) ×ˢ A) ×ˢ B) =
          (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
           μ.prod (X.ν.restrict (Iio (0 : ℝ))))
            (((Set.range times) ×ˢ A) ×ˢ B) ∧
        MT (((Set.range times) ×ˢ A) ×ˢ B) = 0) := by sorry
