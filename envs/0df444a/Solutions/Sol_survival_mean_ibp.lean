-- Prove2me | solution 1 for survival_mean_ibp
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T20:04:53.149754+00:00
-- url     : https://prove2.me/submissions/6e0593d7-e2fc-467e-a1d0-909d31cc2d9f

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
open MeasureTheory Set Filter Topology

/-- **Survival-function mean identity (improper integration by parts).**
For `F : ℝ → ℝ` the CDF of a nonnegative random variable with density `f` (`HasDerivAt F (f x) x`),
`E[T] = ∫₀^∞ t·f(t) dt = ∫₀^∞ (1 - F(t)) dt`, provided the boundary term `t·(1-F(t)) → 0` as
`t → ∞` and the two integrands are integrable on `(0,∞)`.  The `t → 0⁺` boundary contributes `0`
automatically.  This is the standard layer-cake / tail-integral identity for a nonnegative RV. -/
theorem solution (F f : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hint_tf : IntegrableOn (fun t => t * f t) (Ioi (0:ℝ)))
    (hint_surv : IntegrableOn (fun t => 1 - F t) (Ioi (0:ℝ)))
    (hdecay : Tendsto (fun t => t * (1 - F t)) atTop (𝓝 0)) :
    ∫ t in Ioi (0:ℝ), t * f t = ∫ t in Ioi (0:ℝ), (1 - F t) := by
  -- IBP with u(t) = t, v(t) = 1 - F t, u'(t) = 1, v'(t) = -f t.
  set u : ℝ → ℝ := fun t => t with hu_def
  set v : ℝ → ℝ := fun t => 1 - F t with hv_def
  set u' : ℝ → ℝ := fun _ => (1:ℝ) with hu'_def
  set v' : ℝ → ℝ := fun t => -f t with hv'_def
  have hu : ∀ x ∈ Ioi (0:ℝ), HasDerivAt u (u' x) x := by
    intro x _; exact hasDerivAt_id' x
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt v (v' x) x := by
    intro x _
    have := (hF x).const_sub 1
    simpa [hv_def, hv'_def] using this
  have huv' : IntegrableOn (u * v') (Ioi (0:ℝ)) := by
    have : (u * v') = (fun t => t * (-f t)) := by
      funext t; simp [hu_def, hv'_def, Pi.mul_apply]
    rw [this]
    have : (fun t => t * (-f t)) = (fun t => -(t * f t)) := by funext t; ring
    rw [this]; exact hint_tf.neg
  have hu'v : IntegrableOn (u' * v) (Ioi (0:ℝ)) := by
    have : (u' * v) = (fun t => 1 - F t) := by
      funext t; simp [hu'_def, hv_def, Pi.mul_apply]
    rw [this]; exact hint_surv
  have h_zero : Tendsto (u * v) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hFcont : Continuous F := by
      apply continuous_iff_continuousAt.mpr
      intro x; exact (hF x).continuousAt
    have h1 : Continuous u := continuous_id'
    have h2 : Continuous v := continuous_const.sub hFcont
    have huvcont : Continuous (u * v) := by
      simpa [Pi.mul_def] using h1.mul h2
    have hat0 : Tendsto (u * v) (𝓝 (0:ℝ)) (𝓝 ((u * v) 0)) := huvcont.continuousAt
    have hval : (u * v) 0 = 0 := by simp [hu_def, hv_def, Pi.mul_apply]
    rw [hval] at hat0
    exact hat0.mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (u * v) atTop (𝓝 (0:ℝ)) := by
    have : (u * v) = (fun t => t * (1 - F t)) := by
      funext t; simp [hu_def, hv_def, Pi.mul_apply]
    rw [this]; exact hdecay
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  -- key : ∫ u·v' = 0 - 0 - ∫ u'·v
  simp only [sub_zero, zero_sub] at key
  -- ∫ t·(-f) = -∫ (1-F)
  have lhs_eq : ∫ x in Ioi (0:ℝ), u x * v' x = -∫ t in Ioi (0:ℝ), t * f t := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; simp only [hu_def, hv'_def]; ring
  have rhs_eq : ∫ x in Ioi (0:ℝ), u' x * v x = ∫ t in Ioi (0:ℝ), (1 - F t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; simp [hu'_def, hv_def]
  rw [lhs_eq, rhs_eq] at key
  linarith [key]
