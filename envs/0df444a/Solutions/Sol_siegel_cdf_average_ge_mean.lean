-- Prove2me | solution 1 for siegel_cdf_average_ge_mean
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T15:43:06.752813+00:00
-- url     : https://prove2.me/submissions/88be18a5-f77d-4ec3-bc8f-261c2bbd6af4

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

theorem solution (μ : ℝ) (hμ : 0 ≤ μ) (F f : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Ici (0:ℝ), HasDerivAt F (f x) x)
    (hfnn : ∀ x ∈ Set.Ici (0:ℝ), 0 ≤ f x)
    (hF0 : F 0 = 0)
    (hf_int_loc : ∀ b : ℝ, IntervalIntegrable f MeasureTheory.volume 0 b)
    (hf_mass : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)))
    (htf_mass : MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi (0:ℝ)))
    (hmass : ∫ t in Set.Ioi (0:ℝ), f t = 1)
    (hmean : ∫ t in Set.Ioi (0:ℝ), t * f t = μ) :
    μ ≤ ∫ t in (0:ℝ)..(2*μ), F t := by
  set b := 2 * μ with hb_def
  have hb : 0 ≤ b := by positivity
  have hF_uIcc : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt F (f x) x := by
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    exact hF x (Set.mem_Ici.mpr (le_trans (le_refl 0) hx.1))
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt (fun t => t - b) (1 : ℝ) x := by
    intro x _; simpa using (hasDerivAt_id x).sub_const b
  have hv' : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 0 b :=
    _root_.intervalIntegrable_const
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hF_uIcc hv (hf_int_loc b) hv'
  simp only [mul_one] at key
  have hbb : (b - b) = (0:ℝ) := by ring
  rw [hbb, hF0] at key
  simp only [mul_zero, zero_mul, sub_zero, zero_sub] at key
  have hIBP : ∫ t in (0:ℝ)..b, F t = ∫ t in (0:ℝ)..b, (b - t) * f t := by
    rw [key, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr; intro x _; simp only; ring
  have hloc_f : MeasureTheory.IntegrableOn f (Set.Ioc 0 b) := by
    have := (hf_int_loc b)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb] at this; exact this
  have hloc_tf : MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioc 0 b) := by
    exact htf_mass.mono_set (Set.Ioc_subset_Ioi_self)
  have hsplit_set : ∫ t in (0:ℝ)..b, (b - t) * f t
      = b * (∫ t in Set.Ioc (0:ℝ) b, f t) - ∫ t in Set.Ioc (0:ℝ) b, t * f t := by
    rw [intervalIntegral.integral_of_le hb]
    rw [← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_sub]
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x _; simp only; ring
    · exact hloc_f.const_mul b
    · exact hloc_tf
  have hUnion : Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) b ∪ Set.Ioi b := by
    rw [Set.Ioc_union_Ioi_eq_Ioi hb]
  have hdisj : Disjoint (Set.Ioc (0:ℝ) b) (Set.Ioi b) := Set.Ioc_disjoint_Ioi le_rfl
  have hf_Ioib : MeasureTheory.IntegrableOn f (Set.Ioi b) :=
    hf_mass.mono_set (by rw [hUnion]; exact Set.subset_union_right)
  have htf_Ioib : MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi b) :=
    htf_mass.mono_set (by rw [hUnion]; exact Set.subset_union_right)
  have hmass_split : (∫ t in Set.Ioc (0:ℝ) b, f t) + (∫ t in Set.Ioi b, f t) = 1 := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hloc_f hf_Ioib, ← hUnion, hmass]
  have hmean_split : (∫ t in Set.Ioc (0:ℝ) b, t * f t) + (∫ t in Set.Ioi b, t * f t) = μ := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hloc_tf htf_Ioib, ← hUnion, hmean]
  have htail_nn : 0 ≤ (∫ t in Set.Ioi b, t * f t) - b * (∫ t in Set.Ioi b, f t) := by
    have hbm : b * (∫ t in Set.Ioi b, f t) = ∫ t in Set.Ioi b, b * f t := by
      rw [MeasureTheory.integral_const_mul]
    rw [hbm, ← MeasureTheory.integral_sub htf_Ioib (hf_Ioib.const_mul b)]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro x hx
    have hxb : b ≤ x := le_of_lt hx
    have hfx : 0 ≤ f x := hfnn x (Set.mem_Ici.mpr (le_trans hb hxb))
    have hpos : (0:ℝ) ≤ (x - b) * f x := mul_nonneg (by linarith) hfx
    simpa [mul_comm, mul_sub] using hpos
  rw [hIBP, hsplit_set]
  have e1 : (∫ t in Set.Ioc (0:ℝ) b, f t) = 1 - (∫ t in Set.Ioi b, f t) := by
    linarith [hmass_split]
  have e2 : (∫ t in Set.Ioc (0:ℝ) b, t * f t) = μ - (∫ t in Set.Ioi b, t * f t) := by
    linarith [hmean_split]
  rw [e1, e2]
  have hbval : b = 2 * μ := hb_def
  nlinarith [htail_nn, hbval]
