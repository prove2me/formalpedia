-- Prove2me | solution 1 for section5_continuous_event_stability
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:35.14836+00:00
-- url     : https://prove2.me/submissions/13b93daf-9df6-4a72-98c5-e6169e04e27b

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
import Theorems.Thm_section5_l2_norm_sq
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! The sampled Gaussian amplitude and its error before normalization. -/











theorem section5_integral_indicator_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s) (f : α → ℂ) :
    (∫ x, ‖s.indicator f x‖^2 ∂μ) = ∫ x in s, ‖f x‖^2 ∂μ := by
  have heq : (fun x => ‖s.indicator f x‖^2) = s.indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq,integral_indicator hs]



end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory

/-! Event-probability stability for continuous pure states in L2. -/

theorem section5_indicator_l2_norm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Set α) (hs : MeasurableSet s) (f : α → ℂ) (hf : MemLp f 2 μ) :
    ‖(hf.indicator hs).toLp (s.indicator f)‖ ≤ ‖hf.toLp f‖ := by
  have hsq : ‖(hf.indicator hs).toLp (s.indicator f)‖^2 ≤ ‖hf.toLp f‖^2 := by
    rw [section5_l2_norm_sq,section5_l2_norm_sq,section5_integral_indicator_norm_sq s hs]
    exact setIntegral_le_integral hf.norm.integrable_sq
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))
  nlinarith [norm_nonneg ((hf.indicator hs).toLp (s.indicator f)),norm_nonneg (hf.toLp f)]

theorem section5_indicator_l2_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Set α) (hs : MeasurableSet s) (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (hf.indicator hs).toLp (s.indicator f)-(hg.indicator hs).toLp (s.indicator g) =
      ((hf.sub hg).indicator hs).toLp (s.indicator (f-g)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub ((hf.indicator hs).toLp (s.indicator f))
      ((hg.indicator hs).toLp (s.indicator g)),
    (hf.indicator hs).coeFn_toLp,(hg.indicator hs).coeFn_toLp,
    ((hf.sub hg).indicator hs).coeFn_toLp] with x hsub hx hy hz
  rw [hsub,hz]
  change (hf.indicator hs).toLp (s.indicator f) x-(hg.indicator hs).toLp (s.indicator g) x = _
  rw [hx,hy]
  by_cases hxs : x ∈ s <;> simp [hxs]



end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory
theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Set α) (hs : MeasurableSet s) (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ‖hf.toLp f‖ ≤ 1) (hgn : ‖hg.toLp g‖ ≤ 1) :
    |(∫ x in s, ‖f x‖^2 ∂μ)-(∫ x in s, ‖g x‖^2 ∂μ)| ≤
      2*‖hf.toLp f-hg.toLp g‖ := by
  let x := (hf.indicator hs).toLp (s.indicator f)
  let y := (hg.indicator hs).toLp (s.indicator g)
  have hx : ‖x‖ ≤ 1 := (section5_indicator_l2_norm s hs f hf).trans hfn
  have hy : ‖y‖ ≤ 1 := (section5_indicator_l2_norm s hs g hg).trans hgn
  have hxy : ‖x-y‖ ≤ ‖hf.toLp f-hg.toLp g‖ := by
    change ‖(hf.indicator hs).toLp (s.indicator f)-(hg.indicator hs).toLp (s.indicator g)‖ ≤ _
    rw [section5_indicator_l2_sub s hs f g hf hg]
    exact section5_indicator_l2_norm s hs (f-g) (hf.sub hg)
  have hfx : (∫ z in s, ‖f z‖^2 ∂μ)=‖x‖^2 := by
    rw [section5_l2_norm_sq,section5_integral_indicator_norm_sq s hs]
  have hgy : (∫ z in s, ‖g z‖^2 ∂μ)=‖y‖^2 := by
    rw [section5_l2_norm_sq,section5_integral_indicator_norm_sq s hs]
  rw [hfx,hgy]
  calc
    _ = |‖x‖-‖y‖| * (‖x‖+‖y‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)),← abs_mul]
      congr 1
      ring
    _ ≤ ‖x-y‖*2 := mul_le_mul (abs_norm_sub_norm_le x y) (by linarith)
      (add_nonneg (norm_nonneg x) (norm_nonneg y)) (norm_nonneg _)
    _ ≤ _ := by nlinarith
