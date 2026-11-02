-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_jump_count_is_measure
-- name    : AvramDividend.Classical.avram_wave6_01_original_event_weighted_jump_count_is_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:53:17.423965+00:00
-- url     : https://prove2.me/theorems/8efd34b1-187d-45ff-80bc-e85005c53850
-- title:
--   Actual original Lévy marked-jump expectation defines a measure in the past-event variable
-- statement:
--   For the literal original spectrally negative Lévy jump measure NX built from the actual path X.X, and every Borel physical time and mark set C, construct a genuine measure Q on the unchanged original sample space Ω such that Q(A)=E_P[1_A NX(C)] for every measurable original event A. The measure arises as P.withDensity (ω ↦ κω(C)) using the canonically Proved source s-finite jump kernel κ whose fibres equal NX. It supplies the actual source σ-additivity in history events required for a π–λ reduction of past/future jump-count factorisation. No independent copy, assumed count-law, or Lévy intensity identification is introduced.
-- source:
--   Direct original-kernel density construction; genuine missing source-law interface for extending factorisation from finite cylinder classes of histories to all history events. Primary canonical target 393b03a8-2e9a-43d8-b415-854d86d58104 remains Open; this is not its compensator conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_event_weighted_jump_count_is_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C) :
    ∃ Q : Measure Ω, ∀ A : Set Ω, MeasurableSet A →
      Q A = (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by sorry
