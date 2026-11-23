-- Prove2me | solution 1 for kyprianou82_psi_zero_from_coupling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:34:17.886281+00:00
-- url     : https://prove2.me/submissions/e0b7d55e-a7c6-47cd-96ac-08a509058c7e

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    : ψ 0 = 0 := by
  rcases source_result81_filtered_avram_model Ω P D ψ hψ with ⟨F, A, hAX, hAψ⟩
  let hAnot : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)) := by
    intro hanti
    apply D.excludesNegativeSubordinator
    filter_upwards [hAX, hanti] with ω hp ha
    intro s t hst
    simpa [hp s, hp t] using ha hst
  let hA0 : A.ψ 0 = 0 := (source_result81_levy_root_domain A hAnot).1
  rw [← hAψ 0 le_rfl]
  exact hA0
