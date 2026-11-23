-- Prove2me | solution 1 for kyprianou82_actualHeight_zero_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:23:11.25183+00:00
-- url     : https://prove2.me/submissions/062f65e5-4b7f-4a46-938e-570d96bde2f4

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_kyprianou82_actualHeight_pos_raw
import Theorems.Thm_kyprianou82_actualHeight_phi_nat_tendsto
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
  (hW : HasSourceScaleFamily ψ W)
    : (∫ ω, discountedAt 0 (tauPlus D.X 1 ω) ∂P) = Real.exp (-(Phi ψ 0 * 1)) := by
  let qn := fun n : ℕ => 1 / ((n : ℝ) + 1)
  let  hqnpos (n : ℕ) : 0 < qn n := by dsimp [qn]; positivity
  let  hq_tendsto : Tendsto qn atTop (nhds 0) := by
    simpa [qn] using (@tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _)
  let  hPhiTendsto : Tendsto (fun n => Phi ψ (qn n)) atTop (nhds (Phi ψ 0)) := by
    simpa [qn] using kyprianou82_actualHeight_phi_nat_tendsto P D ψ W hψ hW
  let τ := fun ω => tauPlus D.X 1 ω
  let  hpoint (ω) : Tendsto (fun n => discountedAt (qn n) (τ ω)) atTop (nhds (discountedAt 0 (τ ω))) := by
    cases ht : τ ω using WithTop.recTopCoe with
    | top => simp [discountedAt, ht]
    | coe t =>
      have hmul := hq_tendsto.mul_const (t : ℝ)
      have hlim : Tendsto (fun n => Real.exp (-(qn n * (t : ℝ)))) atTop (nhds 1) := by
        change Tendsto (Real.exp ∘ fun n => -(qn n * (t : ℝ))) atTop (nhds 1)
        simpa only [Real.exp_zero] using
          (Real.continuous_exp.tendsto 0).comp (by simpa using hmul.neg)
      simpa [discountedAt, ht] using hlim
  let  hFnint (n : ℕ) : Integrable (fun ω => discountedAt (qn n) (τ ω)) P :=
    (original_unrestricted_upcrossing_discount_bound_zero_included P D ψ W hψ hW (qn n) (hqnpos n).le).1
  have hunit (r : ℝ) (hr : 0 ≤ r) (t : WithTop ℝ≥0) : ‖discountedAt r t‖ ≤ (1 : ℝ) := by
    induction t using WithTop.recTopCoe with
    | top => simp [discountedAt]
    | coe s =>
      simpa [discountedAt, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff] using
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) s.coe_nonneg
  let  hIntTendsto : Tendsto (fun n => ∫ ω, discountedAt (qn n) (τ ω) ∂P) atTop (nhds (∫ ω, discountedAt 0 (τ ω) ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω => (1 : ℝ)) ?_
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P) ?_ ?_
    · intro n; exact (hFnint n).aestronglyMeasurable
    · intro n; exact ae_of_all _ (fun ω => hunit (qn n) (hqnpos n).le (τ ω))
    · exact ae_of_all _ hpoint
  let  hseq (n : ℕ) : (∫ ω, discountedAt (qn n) (τ ω) ∂P) = Real.exp (-(Phi ψ (qn n) * 1)) := by
    simpa [τ] using kyprianou82_actualHeight_pos_raw P D ψ W hψ hW (qn n) (hqnpos n)
  let  hExpTendsto : Tendsto (fun n => Real.exp (-(Phi ψ (qn n) * 1))) atTop (nhds (Real.exp (-(Phi ψ 0 * 1)))) := by
    have hlin : Tendsto (fun n => -(Phi ψ (qn n) * 1)) atTop (nhds (-(Phi ψ 0 * 1))) := by simpa using (hPhiTendsto.mul_const (1 : ℝ)).neg
    exact (Real.continuous_exp.tendsto (-(Phi ψ 0 * 1))).comp hlin
  exact tendsto_nhds_unique (by simpa [hseq] using hIntTendsto) hExpTendsto
