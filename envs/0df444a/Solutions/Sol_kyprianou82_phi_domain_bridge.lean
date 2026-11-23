-- Prove2me | solution 1 for kyprianou82_phi_domain_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:37:42.428808+00:00
-- url     : https://prove2.me/submissions/47694172-2725-4ed7-89a2-5ea5262ae5d6

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
  (hW : HasSourceScaleFamily ψ W)
    : ∀ r : ℝ, 0 ≤ r → IsScaleTransformDomainBridge ψ r := by
  rcases source_result81_filtered_avram_model Ω P D ψ hψ with ⟨F, A, hAX, hAψ⟩
  let hAnot : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)) := by
    intro hanti
    apply D.excludesNegativeSubordinator
    filter_upwards [hAX, hanti] with ω hp ha
    intro s t hst
    simpa [hp] using ha hst
  let hPhiEq (r : ℝ) (hr : 0 ≤ r) : Phi A.ψ r = Phi ψ r := by
    unfold Phi RightRootSet
    congr 1
    ext β
    constructor
    · rintro ⟨hβ, hroot⟩
      exact ⟨hβ, by rw [← hAψ β hβ]; exact hroot⟩
    · rintro ⟨hβ, hroot⟩
      exact ⟨hβ, by rw [hAψ β hβ]; exact hroot⟩
  intro r hr
  let hb := (source_result81_levy_root_domain A hAnot).2 r hr
  refine ⟨(hW r hr).1, ?_⟩
  intro β hβ
  let h := hb.2 β hβ
  rw [hPhiEq r hr] at h
  simpa [hAψ β hβ] using h
