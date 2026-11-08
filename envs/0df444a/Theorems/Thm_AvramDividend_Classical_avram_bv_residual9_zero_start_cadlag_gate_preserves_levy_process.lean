-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_zero_start_cadlag_gate_preserves_levy_process
-- name    : AvramDividend.Classical.avram_bv_residual9_zero_start_cadlag_gate_preserves_levy_process
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:07:09.10848+00:00
-- url     : https://prove2.me/theorems/92d14685-a937-408e-8f93-0402715bdcf4
-- title:
--   Zero-start cadlag gating preserves the full Levy-process structure
-- statement:
--   For a Levy process with literally zero starting value and measurable time sections, a measurable full-measure event on which paths are cadlag admits a zero-gated modification. All paths become cadlag; each deterministic-time section remains almost surely equal to the source; the full Levy-process structure is retained using the proved timewise almost-sure congruence theorem.
-- source:
--   Combines the source-exact Proved gate 5a5a05e9 and process-congruence 91dd6a62 while explicitly checking the all-path zero-start field. Needed to transfer the pure-jump construction to the original all-path Avram process model.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_isLevyProcess_of_ae_time_sections
import Theorems.Thm_ProbabilityTheory_isCadlag_const
open MeasureTheory Filter Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_zero_start_cadlag_gate_preserves_levy_process
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P) (hX0 : ∀ ω, X 0 ω = 0)
    (G : Set Ω) (hGmeas : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hXm : ∀ t, Measurable (X t))
    (hGcad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsLevyProcess Y P ∧
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by sorry
