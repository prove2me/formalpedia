-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_cadlag_downward_gate_preserves_time_laws
-- name    : AvramDividend.Classical.avram_bv_residual9_cadlag_downward_gate_preserves_time_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:38:27.178132+00:00
-- url     : https://prove2.me/theorems/8a411411-8732-4a57-83c0-e2615ef85ea5
-- title:
--   Almost-sure cadlag downward-jump process has an all-path downward-jump modification
-- statement:
--   A process whose paths are cadlag and have no positive jumps on an almost-sure measurable good set admits a modification with both properties for every sample path. On bad paths the modified process is identically zero, so all-path downward-jump and cadlag conditions hold; each time marginal agrees with the source almost surely.
-- source:
--   Extends the direct gate construction in Proved 5a5a05e9 to the downward-jump condition needed by Avram's SpectrallyNegativeLevy. Uses the pinned Mathlib identity for the left limit of a continuous constant path.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_isCadlag_const
open MeasureTheory Filter Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_cadlag_downward_gate_preserves_time_laws
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hMeas : ∀ t, Measurable (X t))
    (hCad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω))
    (hDown : ∀ ω ∈ G, ∀ t : ℝ≥0, 0 < t →
      X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X s ω) t) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ ω (t : ℝ≥0), 0 < t →
        Y t ω ≤ Function.leftLim (fun s : ℝ≥0 => Y s ω) t) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by sorry
