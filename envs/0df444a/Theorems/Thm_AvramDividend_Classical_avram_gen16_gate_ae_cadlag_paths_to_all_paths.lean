-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen16_gate_ae_cadlag_paths_to_all_paths
-- name    : AvramDividend.Classical.avram_gen16_gate_ae_cadlag_paths_to_all_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:25:39.80552+00:00
-- url     : https://prove2.me/theorems/5a5a05e9-4e08-41a3-a20b-c498ed2609a5
-- title:
--   A measurable almost-sure cadlag good event yields a pathwise cadlag modification with unchanged time marginals
-- statement:
--   Given a measurable almost-sure event on which all paths of a real-valued process are cadlag, the process can be gated to zero outside that event. The resulting process has cadlag paths for every sample point, retains measurable time slices and agrees almost everywhere at every time. This supplies a precise regularity step towards Avram's pathwise process structure; jump sign, filtration independence and Laplace moments require separate work.
-- source:
--   LeanLevy/Processes/Cadlag.lean, and existing public Prove2Me theorem f9894139-8d1d-45d5-8a65-ee832a7cc600. Source exercise of the generic good-event gating step in Avram's stronger pathwise model.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_isCadlag_const
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen16_gate_ae_cadlag_paths_to_all_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hMeas : ∀ t, Measurable (X t))
    (hCad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by sorry
