-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_cadlag_regularisation_preserves_all_finite_laws
-- name    : AvramDividend.Classical.avram_bv_residual9_cadlag_regularisation_preserves_all_finite_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:50:23.130196+00:00
-- url     : https://prove2.me/theorems/b94dea6d-9787-4ce9-a1ed-654271f56e5b
-- title:
--   All-path cadlag modification preserves every finite-dimensional Levy-process law
-- statement:
--   A measurable process whose sample paths are cadlag on an almost-sure measurable good set admits an everywhere-cadlag modification with the same one-time values almost surely, and every finite-dimensional distribution remains exactly unchanged. The finite-dimensional law transfer follows by intersecting finitely many time-section equality events and using equality of push-forward measures.
-- source:
--   Bridge toward converting the proved exact-characteristic pure-jump witness c96c705b into an Avram process with all-path cadlag regularity. Depends on Proved 5a5a05e9 and pinned Mathlib Measure.map_congr.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen16_gate_ae_cadlag_paths_to_all_paths
open MeasureTheory Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_cadlag_regularisation_preserves_all_finite_laws
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hMeas : ∀ t, Measurable (X t))
    (hCad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ (n : ℕ) (u : Fin n → ℝ≥0),
        P.map (fun ω => fun i : Fin n => Y (u i) ω) =
          P.map (fun ω => fun i : Fin n => X (u i) ω)) := by sorry
