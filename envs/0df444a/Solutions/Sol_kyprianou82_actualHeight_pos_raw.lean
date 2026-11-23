-- Prove2me | solution 1 for kyprianou82_actualHeight_pos_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:43:05.610917+00:00
-- url     : https://prove2.me/submissions/5c79e84a-c692-4edd-998c-2d1bf50b7909

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_stageB_tauPlus_coe_eq
import Theorems.Thm_kyprianou82_psi_zero_from_coupling
import Theorems.Thm_kyprianou82_discountedAt_nonneg
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
  (hW : HasSourceScaleFamily ψ W)
  (q : ℝ) (hq : 0 < q) :
    (∫ ω, discountedAt q (tauPlus D.X 1 ω) ∂P) = Real.exp (-(Phi ψ q * 1)) := by
  rcases source_result81_filtered_avram_model Ω P D ψ hψ with ⟨F, A, hAX, hAψ⟩
  rcases ((hW q hq.le).1).2.1 with ⟨hφ, hrootψ⟩
  let  hψ0 : ψ 0 = 0 := kyprianou82_psi_zero_from_coupling P D ψ hψ
  let  hφpos : 0 < Phi ψ q := lt_of_le_of_ne hφ fun h => by
    have : ψ 0 = q := by simpa [← h] using hrootψ
    linarith
  let  hAroot : A.ψ (Phi ψ q) = q := by simpa [hAψ (Phi ψ q) hφ] using hrootψ
  let  hExact := levy_positive_root_exact_strict_upcrossing_discount A q hq (Phi ψ q) hφpos hAroot 1 (by norm_num)
  let f := fun ω => discountedAt q (tauPlus A.X 1 ω)
  let  hclock (ω) : (tauPlus A.X 1 ω : ℝ≥0∞) = twoSidedExitUpTimeCorrected A 1 ω := by
    simpa only [twoSidedExitUpTimeCorrected, twoSidedExitUpTime] using stageB_tauPlus_coe_eq A 1 ω
  let  hpoint (ω) : ENNReal.ofReal (f ω) = if twoSidedExitUpTimeCorrected A 1 ω < ⊤ then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTimeCorrected A 1 ω).toReal))) else 0 := by
    rw [← hclock ω]
    cases ht : tauPlus A.X 1 ω using WithTop.recTopCoe with
    | top =>
      simp [f, discountedAt, ht]
      intro htop
      exact (lt_irrefl _ htop).elim
    | coe t => simp [f, discountedAt, ht]
  let  hfnon (ω) : 0 ≤ f ω := by
    simpa [f] using kyprianou82_discountedAt_nonneg q hq.le (tauPlus A.X 1 ω)
  let  hpath : f =ᵐ[P] fun ω => discountedAt q (tauPlus D.X 1 ω) := by
    filter_upwards [hAX] with ω hω
    have ht : tauPlus A.X 1 ω = tauPlus D.X 1 ω := by simp [tauPlus, hω]
    simp [f, ht]
  let hfintD : Integrable (fun ω => discountedAt q (tauPlus D.X 1 ω)) P :=
    (original_unrestricted_upcrossing_discount_bound_zero_included P D ψ W hψ hW q hq.le).1
  let hfint : Integrable f P := hfintD.congr hpath.symm
  let  hlin : ENNReal.ofReal (∫ ω, f ω ∂P) = ENNReal.ofReal (Real.exp (-(Phi ψ q * 1))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (ae_of_all _ hfnon)]
    calc
      (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) = ∫⁻ ω, if twoSidedExitUpTimeCorrected A 1 ω < ⊤ then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTimeCorrected A 1 ω).toReal))) else 0 ∂P := lintegral_congr hpoint
      _ = ENNReal.ofReal (Real.exp (-(Phi ψ q * 1))) := by simpa [hAroot] using hExact
  let hfiltered : (∫ ω, f ω ∂P) = Real.exp (-(Phi ψ q * 1)) :=
    (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun ω => hfnon ω) (Real.exp_pos _).le).mp hlin
  rw [← integral_congr_ae hpath]
  exact hfiltered
