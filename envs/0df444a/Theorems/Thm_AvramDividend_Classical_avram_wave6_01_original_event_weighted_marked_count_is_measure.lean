-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure
-- name    : AvramDividend.Classical.avram_wave6_01_original_event_weighted_marked_count_is_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:14:27.271789+00:00
-- url     : https://prove2.me/theorems/4a1a5c10-7a55-4fe0-886a-73d7e4e53f0a
-- title:
--   Original event-weighted intrinsic Lévy jump count forms a Borel time-mark measure
-- statement:
--   For the actual sample-path jump measure on the unchanged original space Ω, weighting its physical time-mark counts by any measurable original event A gives a genuine measure on time and marks. Its value at each Borel time-mark set C is exactly the original expectation E[1_A N_X(C)], even if this expectation is infinite. The construction is the bind of P restricted to A with the canonically Proved original s-finite jump kernel. This yields sigma-additivity and monotone-limit compatibility in the mark variable without assuming the Lévy intensity compensator or a proxy Poisson model.
-- source:
--   Canonically Proved original source s-finite kernel eb357d08-4af6-409d-a410-b001723c0008; use Measure.bind_apply and kernel measurability. Source Markov/measure-law interface distinct from the still-Open arbitrary-mark compensator 393b03a8-2e9a-43d8-b415-854d86d58104.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_event_weighted_marked_count_is_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∃ M : Measure (ℝ≥0 × ℝ),
      ∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        M C = (∫⁻ ω in A,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by sorry
