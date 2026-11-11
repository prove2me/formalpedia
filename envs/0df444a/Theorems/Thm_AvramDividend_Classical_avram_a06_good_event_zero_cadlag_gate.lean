-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_good_event_zero_cadlag_gate
-- name    : AvramDividend.Classical.avram_a06_good_event_zero_cadlag_gate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:24:28.714051+00:00
-- url     : https://prove2.me/theorems/a6c66379-3a00-4614-a834-6612552cb3bb
-- title:
--   Measurable full-measure good-event gate produces all-path zero-start cadlag Lévy modification
-- statement:
--   Given a Lévy process whose initial value and càdlàg paths hold on one measurable full-measure event, replace paths outside that event by zero. The modification starts at zero on every path, is càdlàg everywhere, remains a Lévy process by the proved AE time-section congruence theorem, and equals the original at every deterministic time almost surely. This weakens the older gate's globally zero-start assumption, needed for original compound Poisson.
-- source:
--   Root-connected source regularisation ingredient for the A06 filtered gate 962fdfab and original source certificate d4e19a1a.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_isLevyProcess_of_ae_time_sections
import Theorems.Thm_ProbabilityTheory_isCadlag_const
open MeasureTheory Filter Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_good_event_zero_cadlag_gate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (G : Set Ω) (hGmeas : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hXm : ∀ t, Measurable (X t))
    (hGzero : ∀ ω ∈ G, X 0 ω = 0)
    (hGcad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsLevyProcess Y P ∧
      (∀ ω, Y 0 ω = 0) ∧
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by sorry
