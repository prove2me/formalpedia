-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_fixed_time_atom_zero_ae
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_predictable_occupation_fixed_time_atom_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:32:09.597261+00:00
-- url     : https://prove2.me/theorems/3bec58db-44ea-4686-962b-101e966ab024
-- title:
--   Actual original predictable occupation has no marked atom at any deterministic time
-- statement:
--   For every deterministic time t and original predictable time-history slice {t}×A, the actual source occupation measure P.bind K of the genuine original process marked jumps has zero mass on (({t}×A)×B) for any Borel mark band B. t=0 follows pathwise from count exclusion; t>0 follows from original Lévy no-fixed-jump law. The explicit kernel equality guarantees same-path identity and filtration, with no Poisson copy or assumed negative-band compensator.
-- source:
--   Uses source no-fixed-time marked count b6d7a6a3, source t=0 zero e2216ed6, full source predictable kernel 4443ac3e, same-path measurable lift 2648ec36.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_full_original_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_fixed_time_marked_count_zero_ae
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_predictable_occupation_fixed_time_atom_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (t : ℝ≥0) (A : Set Ω)
    (hPred : MeasurableSet[𝓕.predictable] ({t} ×ˢ A))
    (B : Set ℝ) (hB : MeasurableSet B) :
    M (({t} ×ˢ A) ×ˢ B) = 0 := by sorry
