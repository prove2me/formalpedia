-- Prove2me | solution 1 for exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e2e94def-176c-50f8-b611-2ebba608a1f5

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Operator.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd

set_option autoImplicit false

open Filter Topology

private noncomputable def whitChi (w : ℝ) : ℝ := Real.smoothTransition (w + 2)

private theorem contDiff_whitChi : ContDiff ℝ (⊤ : ℕ∞) whitChi :=
  Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

private theorem whitChi_of_le {w : ℝ} (hw : w ≤ -2) : whitChi w = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem whitChi_of_ge {w : ℝ} (hw : -1 ≤ w) : whitChi w = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem whitChi_nonneg (w : ℝ) : 0 ≤ whitChi w := Real.smoothTransition.nonneg _

private theorem whitChi_le_one (w : ℝ) : whitChi w ≤ 1 := Real.smoothTransition.le_one _

private noncomputable def whitCCoeff (k : ℕ) : ℝ := (-1) ^ k / ((2 * k).factorial : ℝ)

private noncomputable def whitSCoeff (k : ℕ) : ℝ := (-1) ^ k / ((2 * k + 1).factorial : ℝ)

private noncomputable def whitC : ℝ → ℝ := FormalMultilinearSeries.ofScalarsSum whitCCoeff

private noncomputable def whitS : ℝ → ℝ := FormalMultilinearSeries.ofScalarsSum whitSCoeff

private theorem whitCCoeff_ne_zero (k : ℕ) : whitCCoeff k ≠ 0 := by
  unfold whitCCoeff
  positivity

private theorem whitSCoeff_ne_zero (k : ℕ) : whitSCoeff k ≠ 0 := by
  unfold whitSCoeff
  positivity

private theorem norm_whitCCoeff (k : ℕ) : ‖whitCCoeff k‖ = 1 / ((2 * k).factorial : ℝ) := by
  unfold whitCCoeff
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (Nat.cast_nonneg _)]

private theorem norm_whitSCoeff (k : ℕ) : ‖whitSCoeff k‖ = 1 / ((2 * k + 1).factorial : ℝ) := by
  unfold whitSCoeff
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (Nat.cast_nonneg _)]

private theorem whitCCoeff_ratio_le (k : ℕ) : ‖whitCCoeff (k + 1)‖ / ‖whitCCoeff k‖ ≤ 1 / ((k : ℝ) + 1) := by
  rw [norm_whitCCoeff, norm_whitCCoeff]
  have hf : ((2 * (k + 1)).factorial : ℝ) = (2 * k + 2) * ((2 * k + 1) * ((2 * k).factorial : ℝ)) := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hB : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have h1 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have h2 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hratio : (1 / ((2 * (k + 1)).factorial : ℝ)) / (1 / ((2 * k).factorial : ℝ)) =
      1 / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1)) := by
    rw [hf]
    field
  rw [hratio]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])

private theorem whitSCoeff_ratio_le (k : ℕ) : ‖whitSCoeff (k + 1)‖ / ‖whitSCoeff k‖ ≤ 1 / ((k : ℝ) + 1) := by
  rw [norm_whitSCoeff, norm_whitSCoeff]
  have hf : ((2 * (k + 1) + 1).factorial : ℝ) =
      (2 * k + 3) * ((2 * k + 2) * ((2 * k + 1).factorial : ℝ)) := by
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hB : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
  have h1 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have hratio : (1 / ((2 * (k + 1) + 1).factorial : ℝ)) / (1 / ((2 * k + 1).factorial : ℝ)) =
      1 / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2)) := by
    rw [hf]
    field
  rw [hratio]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])

private theorem whitCCoeff_ratio_tendsto :
    Tendsto (fun k : ℕ => ‖whitCCoeff k.succ‖ / ‖whitCCoeff k‖) atTop (𝓝 0) :=
  squeeze_zero (fun k => by positivity) (fun k => whitCCoeff_ratio_le k) tendsto_one_div_add_atTop_nhds_zero_nat

private theorem whitSCoeff_ratio_tendsto :
    Tendsto (fun k : ℕ => ‖whitSCoeff k.succ‖ / ‖whitSCoeff k‖) atTop (𝓝 0) :=
  squeeze_zero (fun k => by positivity) (fun k => whitSCoeff_ratio_le k) tendsto_one_div_add_atTop_nhds_zero_nat

private theorem whitC_radius : (FormalMultilinearSeries.ofScalars ℝ whitCCoeff).radius = ⊤ :=
  FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto (E := ℝ) (c := whitCCoeff)
    (Eventually.of_forall whitCCoeff_ne_zero) whitCCoeff_ratio_tendsto

private theorem whitS_radius : (FormalMultilinearSeries.ofScalars ℝ whitSCoeff).radius = ⊤ :=
  FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto (E := ℝ) (c := whitSCoeff)
    (Eventually.of_forall whitSCoeff_ne_zero) whitSCoeff_ratio_tendsto

private theorem contDiff_ofScalarsSum_of_radius_eq_top (c : ℕ → ℝ)
    (hc : (FormalMultilinearSeries.ofScalars ℝ c).radius = ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (FormalMultilinearSeries.ofScalarsSum (E := ℝ) c) := by
  have h := (FormalMultilinearSeries.ofScalars ℝ c).hasFPowerSeriesOnBall (by rw [hc]; exact ENNReal.zero_lt_top)
  rw [hc] at h
  have h2 : AnalyticOnNhd ℝ (FormalMultilinearSeries.ofScalarsSum (E := ℝ) c) Set.univ :=
    fun x _ => h.analyticAt_of_mem (by simp)
  exact h2.contDiff

private theorem contDiff_whitC : ContDiff ℝ (⊤ : ℕ∞) whitC := contDiff_ofScalarsSum_of_radius_eq_top _ whitC_radius

private theorem contDiff_whitS : ContDiff ℝ (⊤ : ℕ∞) whitS := contDiff_ofScalarsSum_of_radius_eq_top _ whitS_radius

private theorem whitC_sq (θ : ℝ) : whitC (θ ^ 2) = Real.cos θ := by
  rw [Real.cos_eq_tsum]
  unfold whitC
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  refine tsum_congr fun n => ?_
  unfold whitCCoeff
  rw [smul_eq_mul, ← pow_mul]
  ring

private theorem whitS_sq (θ : ℝ) : θ * whitS (θ ^ 2) = Real.sin θ := by
  rw [Real.sin_eq_tsum]
  unfold whitS
  rw [FormalMultilinearSeries.ofScalars_sum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold whitSCoeff
  rw [smul_eq_mul, ← pow_mul]
  ring

private theorem whitC_zero : whitC 0 = 1 := by
  unfold whitC
  rw [FormalMultilinearSeries.ofScalarsSum_zero]
  simp [whitCCoeff]

private theorem whitS_zero : whitS 0 = 1 := by
  unfold whitS
  rw [FormalMultilinearSeries.ofScalarsSum_zero]
  simp [whitSCoeff]

private theorem whitC_of_nonneg {w : ℝ} (hw : 0 ≤ w) : whitC w = Real.cos (Real.sqrt w) := by
  have h := whitC_sq (Real.sqrt w)
  rwa [Real.sq_sqrt hw] at h

private theorem whitS_of_pos {w : ℝ} (hw : 0 < w) : whitS w = Real.sin (Real.sqrt w) / Real.sqrt w := by
  have h := whitS_sq (Real.sqrt w)
  rw [Real.sq_sqrt hw.le] at h
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  rw [eq_div_iff hs, mul_comm]
  exact h

private theorem whitS_sq_div {θ : ℝ} (hθ : θ ≠ 0) : whitS (θ ^ 2) = Real.sin θ / θ := by
  rw [eq_div_iff hθ, mul_comm]
  exact whitS_sq θ

private theorem whit_iteratedDeriv_congr_of_eventuallyEq {f g : ℝ → ℝ} {w : ℝ} (h : f =ᶠ[𝓝 w] g) (n : ℕ) :
    iteratedDeriv n f =ᶠ[𝓝 w] iteratedDeriv n g := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact ih.deriv

private theorem whit_contDiff_nat {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) : ContDiff ℝ n g :=
  hg.of_le (by exact_mod_cast le_top)

private theorem whit_differentiable_iteratedDeriv {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ) :
    Differentiable ℝ (iteratedDeriv m g) :=
  (whit_contDiff_nat hg (m + 1)).differentiable_iteratedDeriv' m

private theorem whit_continuous_iteratedDeriv {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ) :
    Continuous (iteratedDeriv m g) :=
  (whit_contDiff_nat hg m).continuous_iteratedDeriv' m

private theorem whitC_hasDerivAt {w : ℝ} (hw : 0 < w) : HasDerivAt whitC (-(1 / 2) * whitS w) w := by
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  have h := (Real.hasDerivAt_sqrt hw.ne').cos
  have hev : whitC =ᶠ[𝓝 w] fun u => Real.cos (Real.sqrt u) := by
    filter_upwards [Ioi_mem_nhds hw] with u hu
    exact whitC_of_nonneg (le_of_lt (Set.mem_Ioi.1 hu))
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [whitS_of_pos hw]
  field

private theorem whitS_hasDerivAt_sq {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt whitS ((whitC (θ ^ 2) - whitS (θ ^ 2)) / (2 * θ ^ 2)) (θ ^ 2) := by
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  have hsq := Real.hasDerivAt_sqrt hθ2.ne'
  have hs : Real.sqrt (θ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hθ2).ne'
  have h := hsq.sin.div hsq hs
  have hev : whitS =ᶠ[𝓝 (θ ^ 2)] (fun u => Real.sin (Real.sqrt u)) / (fun u => Real.sqrt u) := by
    filter_upwards [Ioi_mem_nhds hθ2] with u hu
    rw [Pi.div_apply]
    exact whitS_of_pos (Set.mem_Ioi.1 hu)
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [whitC_sq, whitS_sq_div hθ.ne', Real.sqrt_sq hθ.le]
  have hθ0 : θ ≠ 0 := hθ.ne'
  field

private theorem whitS_hasDerivAt {w : ℝ} (hw : 0 < w) : HasDerivAt whitS ((whitC w - whitS w) / (2 * w)) w := by
  have h := whitS_hasDerivAt_sq (Real.sqrt_pos.2 hw)
  rwa [Real.sq_sqrt hw.le] at h

private theorem
    contDiff_deriv_whitS : ContDiff ℝ (⊤ : ℕ∞) (deriv whitS) := (contDiff_infty_iff_deriv.1 contDiff_whitS).2

private theorem iteratedDeriv_succ_id_mul {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : ℕ) :
    iteratedDeriv (j + 1) (fun u => u * g u) =
      fun u => u * iteratedDeriv (j + 1) g u + ((j : ℝ) + 1) * iteratedDeriv j g u := by
  induction j with
  | zero =>
    funext u
    have hd : DifferentiableAt ℝ g u := by
      have h0 := whit_differentiable_iteratedDeriv hg 0
      rw [iteratedDeriv_zero] at h0
      exact h0 u
    have h : HasDerivAt (fun y : ℝ => y * g y) (1 * g u + u * deriv g u) u := (hasDerivAt_id u).mul hd.hasDerivAt
    rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_zero, h.deriv]
    push_cast
    ring
  | succ i ih =>
    funext u
    have h1 : DifferentiableAt ℝ (iteratedDeriv (i + 1) g) u := whit_differentiable_iteratedDeriv hg (i + 1) u
    have h2 : DifferentiableAt ℝ (iteratedDeriv i g) u := whit_differentiable_iteratedDeriv hg i u
    have h : HasDerivAt (fun y : ℝ => y * iteratedDeriv (i + 1) g y + ((i : ℝ) + 1) * iteratedDeriv i g y)
        (1 * iteratedDeriv (i + 1) g u + u * deriv (iteratedDeriv (i + 1) g) u +
          ((i : ℝ) + 1) * deriv (iteratedDeriv i g) u) u :=
      ((hasDerivAt_id u).mul h1.hasDerivAt).add (h2.hasDerivAt.const_mul _)
    rw [iteratedDeriv_succ, ih, h.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
    push_cast
    ring

private theorem iteratedDeriv_succ_whitC {j : ℕ} {w : ℝ} (hw : 0 < w) :
    iteratedDeriv (j + 1) whitC w = -(1 / 2) * iteratedDeriv j whitS w := by
  rw [iteratedDeriv_succ']
  have hev : deriv whitC =ᶠ[𝓝 w] fun u => -(1 / 2) * whitS u := by
    filter_upwards [Ioi_mem_nhds hw] with u hu
    exact (whitC_hasDerivAt (Set.mem_Ioi.1 hu)).deriv
  have e : iteratedDeriv j (deriv whitC) w = iteratedDeriv j (fun u => -(1 / 2) * whitS u) w :=
    (whit_iteratedDeriv_congr_of_eventuallyEq hev j).eq_of_nhds
  rw [e, iteratedDeriv_const_mul_field]

private theorem whit_key_identity (j : ℕ) {w : ℝ} (hw : 0 < w) :
    w * iteratedDeriv (j + 1) (deriv whitS) w + ((j : ℝ) + 1) * iteratedDeriv j (deriv whitS) w =
      (1 / 2) * (iteratedDeriv (j + 1) whitC w - iteratedDeriv (j + 1) whitS w) := by
  have hev : (fun u => u * deriv whitS u) =ᶠ[𝓝 w] fun u => (1 / 2) * (whitC - whitS) u := by
    filter_upwards [Ioi_mem_nhds hw] with u hu
    have hu0 : u ≠ 0 := (Set.mem_Ioi.1 hu).ne'
    rw [(whitS_hasDerivAt (Set.mem_Ioi.1 hu)).deriv, Pi.sub_apply]
    field
  have h1 := congrFun (iteratedDeriv_succ_id_mul contDiff_deriv_whitS j) w
  have e : iteratedDeriv (j + 1) (fun u => u * deriv whitS u) w =
      iteratedDeriv (j + 1) (fun u => (1 / 2) * (whitC - whitS) u) w :=
    (whit_iteratedDeriv_congr_of_eventuallyEq hev (j + 1)).eq_of_nhds
  rw [← h1, e, iteratedDeriv_const_mul_field,
    iteratedDeriv_sub (whit_contDiff_nat contDiff_whitC _).contDiffAt (whit_contDiff_nat contDiff_whitS _).contDiffAt]

private theorem abs_whitC_le_one_of_one_le {w : ℝ} (hw : 1 ≤ w) : |whitC w| ≤ 1 := by
  rw [whitC_of_nonneg (by linarith)]
  exact Real.abs_cos_le_one _

private theorem abs_whitS_le_one_of_one_le {w : ℝ} (hw : 1 ≤ w) : |whitS w| ≤ 1 := by
  have hw0 : 0 < w := by linarith
  have h1 : 1 ≤ Real.sqrt w := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hw
  rw [whitS_of_pos hw0, abs_div, abs_of_pos (Real.sqrt_pos.2 hw0)]
  exact div_le_one_of_le₀ ((Real.abs_sin_le_one _).trans h1) (by linarith)

private theorem abs_deriv_whitS_le_one_of_one_le {w : ℝ} (hw : 1 ≤ w) : |deriv whitS w| ≤ 1 := by
  have hw0 : 0 < w := by linarith
  rw [(whitS_hasDerivAt hw0).deriv, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * w)]
  refine div_le_one_of_le₀ ?_ (by linarith)
  obtain ⟨hC1, hC2⟩ := abs_le.1 (abs_whitC_le_one_of_one_le hw)
  obtain ⟨hS1, hS2⟩ := abs_le.1 (abs_whitS_le_one_of_one_le hw)
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem whit_bounded_on_Ici_one (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℝ, 1 ≤ w →
      |iteratedDeriv j whitC w| ≤ M ∧ |iteratedDeriv j whitS w| ≤ M ∧ |iteratedDeriv j (deriv whitS) w| ≤ M := by
  induction j with
  | zero =>
    refine ⟨1, zero_le_one, fun w hw => ?_⟩
    simp only [iteratedDeriv_zero]
    exact ⟨abs_whitC_le_one_of_one_le hw, abs_whitS_le_one_of_one_le hw, abs_deriv_whitS_le_one_of_one_le hw⟩
  | succ j ih =>
    obtain ⟨M, hM0, hM⟩ := ih
    refine ⟨((j : ℝ) + 2) * M, by positivity, fun w hw => ?_⟩
    have hw0 : 0 < w := by linarith
    obtain ⟨hC, hS, hT⟩ := hM w hw
    have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity

    have hC' : |iteratedDeriv (j + 1) whitC w| ≤ M / 2 := by
      rw [iteratedDeriv_succ_whitC hw0, abs_mul]
      have : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
      rw [this]
      linarith

    have hS' : |iteratedDeriv (j + 1) whitS w| ≤ M := by
      rw [iteratedDeriv_succ']
      exact hT
    have hjM : (0 : ℝ) ≤ (j : ℝ) * M := by positivity
    refine ⟨by linarith, by linarith, ?_⟩

    have hid := whit_key_identity j hw0
    obtain ⟨hC1, hC2⟩ := abs_le.1 hC'
    obtain ⟨hS1, hS2⟩ := abs_le.1 hS'
    obtain ⟨hT1, hT2⟩ := abs_le.1 hT
    have hprod : |w * iteratedDeriv (j + 1) (deriv whitS) w| ≤ ((j : ℝ) + 2) * M := by
      have e1 : w * iteratedDeriv (j + 1) (deriv whitS) w =
          (1 / 2) * (iteratedDeriv (j + 1) whitC w - iteratedDeriv (j + 1) whitS w) -
            ((j : ℝ) + 1) * iteratedDeriv j (deriv whitS) w := by linarith
      rw [e1]
      have hjT1 := mul_le_mul_of_nonneg_left hT2 hj0
      have hjT2 := mul_le_mul_of_nonneg_left hT1 hj0
      exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
    rw [abs_mul, abs_of_pos hw0] at hprod
    calc |iteratedDeriv (j + 1) (deriv whitS) w|
        ≤ w * |iteratedDeriv (j + 1) (deriv whitS) w| := le_mul_of_one_le_left (abs_nonneg _) hw
      _ ≤ ((j : ℝ) + 2) * M := hprod

private theorem whit_bounded_on_Ici (a : ℝ) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℝ, -a ≤ w → |iteratedDeriv j whitC w| ≤ M ∧ |iteratedDeriv j whitS w| ≤ M := by
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := -a) (b := 1)).exists_bound_of_continuousOn
    (whit_continuous_iteratedDeriv contDiff_whitC j).continuousOn
  obtain ⟨M₂, hM₂⟩ := (isCompact_Icc (a := -a) (b := 1)).exists_bound_of_continuousOn
    (whit_continuous_iteratedDeriv contDiff_whitS j).continuousOn
  obtain ⟨M₃, hM₃0, hM₃⟩ := whit_bounded_on_Ici_one j
  refine ⟨max (max M₁ M₂) M₃, le_max_of_le_right hM₃0, fun w hw => ?_⟩
  by_cases h1 : w ≤ 1
  · have hmem : w ∈ Set.Icc (-a) 1 := ⟨hw, h1⟩
    have e1 := hM₁ w hmem
    have e2 := hM₂ w hmem
    rw [Real.norm_eq_abs] at e1 e2
    exact ⟨e1.trans (le_max_of_le_left (le_max_left _ _)), e2.trans (le_max_of_le_left (le_max_right _ _))⟩
  · have h1' : 1 ≤ w := (not_le.1 h1).le
    obtain ⟨e1, e2, -⟩ := hM₃ w h1'
    exact ⟨e1.trans (le_max_right _ _), e2.trans (le_max_right _ _)⟩

private noncomputable def whitK₁ (w : ℝ) : ℝ := whitChi w * whitC (4 * Real.pi ^ 2 * w)

private noncomputable def whitK₂ (w : ℝ) : ℝ := whitChi w * whitS (4 * Real.pi ^ 2 * w)

private theorem whitK₁_apply (w : ℝ) : whitK₁ w = whitChi w * whitC (4 * Real.pi ^ 2 * w) := rfl

private theorem whitK₂_apply (w : ℝ) : whitK₂ w = whitChi w * whitS (4 * Real.pi ^ 2 * w) := rfl

private theorem contDiff_whitK₁ : ContDiff ℝ (⊤ : ℕ∞) whitK₁ :=
  contDiff_whitChi.mul (contDiff_whitC.comp (contDiff_const.mul contDiff_id))

private theorem contDiff_whitK₂ : ContDiff ℝ (⊤ : ℕ∞) whitK₂ :=
  contDiff_whitChi.mul (contDiff_whitS.comp (contDiff_const.mul contDiff_id))

private theorem whitK₁_of_le {w : ℝ} (hw : w ≤ -2) : whitK₁ w = 0 := by
  rw [whitK₁_apply, whitChi_of_le hw, zero_mul]

private theorem whitK₂_of_le {w : ℝ} (hw : w ≤ -2) : whitK₂ w = 0 := by
  rw [whitK₂_apply, whitChi_of_le hw, zero_mul]

private theorem whitK₁_of_nonneg {w : ℝ} (hw : 0 ≤ w) : whitK₁ w = whitC (4 * Real.pi ^ 2 * w) := by
  rw [whitK₁_apply, whitChi_of_ge (by linarith), one_mul]

private theorem whitK₂_of_nonneg {w : ℝ} (hw : 0 ≤ w) : whitK₂ w = whitS (4 * Real.pi ^ 2 * w) := by
  rw [whitK₂_apply, whitChi_of_ge (by linarith), one_mul]

private theorem abs_iteratedDeriv_le_one_of_eventually_const {f : ℝ → ℝ} {w c : ℝ} (hc : |c| ≤ 1)
    (h : f =ᶠ[𝓝 w] fun _ => c) (i : ℕ) : |iteratedDeriv i f w| ≤ 1 := by
  have e : iteratedDeriv i f w = iteratedDeriv i (fun _ => c) w :=
    (whit_iteratedDeriv_congr_of_eventuallyEq h i).eq_of_nhds
  rw [e, iteratedDeriv_const]
  split_ifs
  · exact hc
  · simp

private theorem whitChi_iteratedDeriv_bounded (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℝ, |iteratedDeriv i whitChi w| ≤ B := by
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := -1)).exists_bound_of_continuousOn
    (whit_continuous_iteratedDeriv contDiff_whitChi i).continuousOn
  refine ⟨max B₀ 1, le_max_of_le_right zero_le_one, fun w => ?_⟩
  by_cases h1 : w < -2
  · refine (abs_iteratedDeriv_le_one_of_eventually_const (c := 0) (by simp) ?_ i).trans (le_max_right _ _)
    filter_upwards [Iio_mem_nhds h1] with u hu
    exact whitChi_of_le (le_of_lt (Set.mem_Iio.1 hu))
  by_cases h2 : -1 < w
  · refine (abs_iteratedDeriv_le_one_of_eventually_const (c := 1) (by simp) ?_ i).trans (le_max_right _ _)
    filter_upwards [Ioi_mem_nhds h2] with u hu
    exact whitChi_of_ge (le_of_lt (Set.mem_Ioi.1 hu))
  have e := hB₀ w ⟨not_lt.1 h1, not_lt.1 h2⟩
  rw [Real.norm_eq_abs] at e
  exact e.trans (le_max_left _ _)

private theorem whit_product_iteratedDeriv_bounded (F : ℝ → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFb : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, -(8 * Real.pi ^ 2) ≤ u → |iteratedDeriv m F u| ≤ M) (j : ℕ) :
    ∃ B : ℝ, ∀ w : ℝ, |iteratedDeriv j (fun w => whitChi w * F (4 * Real.pi ^ 2 * w)) w| ≤ B := by
  choose Bχ hBχ0 hBχ using whitChi_iteratedDeriv_bounded
  choose MF hMF0 hMF using hFb
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ => F (4 * Real.pi ^ 2 * w)) := hF.comp (contDiff_const.mul contDiff_id)
  have hgd : ∀ m : ℕ, ∀ w : ℝ, -2 ≤ w →
      |iteratedDeriv m (fun w : ℝ => F (4 * Real.pi ^ 2 * w)) w| ≤ (4 * Real.pi ^ 2) ^ m * MF m := by
    intro m w hw
    rw [iteratedDeriv_comp_const_mul (whit_contDiff_nat hF m), abs_mul, abs_of_nonneg (by positivity)]
    have h4 : -(8 * Real.pi ^ 2) ≤ 4 * Real.pi ^ 2 * w := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2) (by linarith : (0 : ℝ) ≤ w + 2)]
    exact mul_le_mul_of_nonneg_left (hMF m _ h4) (by positivity)
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Bχ i * ((4 * Real.pi ^ 2) ^ (j - i) * MF (j - i)),
    fun w => ?_⟩
  by_cases hw : w < -2
  · have h0 : (fun w => whitChi w * F (4 * Real.pi ^ 2 * w)) =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hw] with u hu
      rw [whitChi_of_le (le_of_lt (Set.mem_Iio.1 hu)), zero_mul]
    have e : iteratedDeriv j (fun w => whitChi w * F (4 * Real.pi ^ 2 * w)) w = iteratedDeriv j (fun _ => (0 : ℝ)) w :=
      (whit_iteratedDeriv_congr_of_eventuallyEq h0 j).eq_of_nhds
    rw [e, iteratedDeriv_const]
    have hsum : (0 : ℝ) ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Bχ i * ((4 * Real.pi ^ 2) ^ (j - i) * MF (j - i)) :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (by positivity) (hBχ0 i)) (mul_nonneg (by positivity) (hMF0 _))
    split_ifs <;> simpa using hsum
  have hw' : -2 ≤ w := not_lt.1 hw
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_mul_le contDiff_whitChi hg w (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hBχ i w) (by positivity)) (hgd (j - i) w hw') (abs_nonneg _)
    (mul_nonneg (by positivity) (hBχ0 i))

private theorem whitK₁_iteratedDeriv_bounded (j : ℕ) : ∃ B : ℝ, ∀ w : ℝ, |iteratedDeriv j whitK₁ w| ≤ B :=
  whit_product_iteratedDeriv_bounded whitC contDiff_whitC
    (fun m => (whit_bounded_on_Ici (8 * Real.pi ^ 2) m).imp fun _ hM => ⟨hM.1, fun u hu => (hM.2 u hu).1⟩) j

private theorem whitK₂_iteratedDeriv_bounded (j : ℕ) : ∃ B : ℝ, ∀ w : ℝ, |iteratedDeriv j whitK₂ w| ≤ B :=
  whit_product_iteratedDeriv_bounded whitS contDiff_whitS
    (fun m => (whit_bounded_on_Ici (8 * Real.pi ^ 2) m).imp fun _ hM => ⟨hM.1, fun u hu => (hM.2 u hu).2⟩) j

private theorem whitK₁_iteratedDeriv_polyGrowth (j : ℕ) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ w : ℝ, |iteratedDeriv j whitK₁ w| ≤ B * (1 + |w|) ^ N :=
  (whitK₁_iteratedDeriv_bounded j).imp fun B hB => ⟨0, fun w => by simpa using hB w⟩

private theorem whitK₂_iteratedDeriv_polyGrowth (j : ℕ) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ w : ℝ, |iteratedDeriv j whitK₂ w| ≤ B * (1 + |w|) ^ N :=
  (whitK₂_iteratedDeriv_bounded j).imp fun B hB => ⟨0, fun w => by simpa using hB w⟩

open MeasureTheory FourierTransform

private noncomputable def whitSchwartz (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    SchwartzMap ℝ ℂ :=
  hc.toSchwartzMap hf

private theorem whitSchwartz_coe (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ⇑(whitSchwartz f hf hc) = f := rfl

private theorem whit_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hc

private theorem
    whit_fourier_pow_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (k : ℕ) :
    Integrable fun τ : ℝ => ‖τ‖ ^ k * ‖𝓕 f τ‖ := by
  have h := (𝓕 (whitSchwartz f hf hc)).integrable_pow_mul volume k
  rwa [SchwartzMap.fourier_coe, whitSchwartz_coe] at h

private theorem whit_fourier_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Integrable (𝓕 f) := by
  have h := (𝓕 (whitSchwartz f hf hc)).integrable (μ := volume)
  rwa [SchwartzMap.fourier_coe, whitSchwartz_coe] at h

private theorem whit_fourier_abs_pow_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (k : ℕ) : Integrable fun τ : ℝ => |τ| ^ k * ‖𝓕 f τ‖ := by
  simpa only [Real.norm_eq_abs] using whit_fourier_pow_integrable hf hc k

private theorem whit_fourierInv_fourier {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    𝓕⁻ (𝓕 f) = f :=
  hf.continuous.fourierInv_fourier_eq (whit_integrable hf hc) (whit_fourier_integrable hf hc)

private theorem whit_inversion {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (x : ℝ) :
    ∫ τ : ℝ, Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ = f x := by
  have h := congrFun (whit_fourierInv_fourier hf hc) x
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

private theorem whit_deriv_zero_of_even {f : ℝ → ℂ} (hf : ∀ x : ℝ, f (-x) = f x) : deriv f 0 = 0 := by
  have h1 : (fun x : ℝ => f (-x)) = f := funext hf
  have h2 := deriv_comp_neg (f := f) (x := (0 : ℝ))
  rw [h1, neg_zero] at h2
  linear_combination (1 / 2 : ℂ) * h2

private noncomputable def whitPsi (y : ℝ) : ℝ := Real.smoothTransition (2 * y + 2)

private theorem contDiff_whitPsi : ContDiff ℝ (⊤ : ℕ∞) whitPsi :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

private theorem whitPsi_of_nonneg {y : ℝ} (hy : 0 ≤ y) : whitPsi y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem whitPsi_of_le {y : ℝ} (hy : y ≤ -1) : whitPsi y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private noncomputable def whitKer (y τ : ℝ) : ℂ :=
  ((whitK₁ (τ ^ 2 * y) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * τ * ((whitK₂ (τ ^ 2 * y) : ℝ) : ℂ)

private noncomputable def whitRaw (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ τ : ℝ, (((whitK₁ (τ ^ 2 * y) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * τ * ((whitK₂ (τ ^ 2 * y) : ℝ) : ℂ)) * 𝓕 f τ

private theorem whitRaw_eq (f : ℝ → ℂ) (y : ℝ) : whitRaw f y = ∫ τ : ℝ, whitKer y τ * 𝓕 f τ := rfl

private noncomputable def whitW (f : ℝ → ℂ) (y : ℝ) : ℂ := ((whitPsi y : ℝ) : ℂ) * whitRaw f y

private theorem whitW_of_le (f : ℝ → ℂ) {y : ℝ} (hy : y ≤ -1) : whitW f y = 0 := by
  rw [whitW, whitPsi_of_le hy, Complex.ofReal_zero, zero_mul]

private theorem whit_tau_mul_fourier_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Integrable fun τ : ℝ => (τ : ℂ) * 𝓕 f τ := by
  refine (whit_fourier_abs_pow_integrable hf hc 1).mono'
    (Complex.continuous_ofReal.aestronglyMeasurable.mul (whit_fourier_integrable hf hc).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun τ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_one]

private theorem whitKernel_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (y : ℝ) :
    Integrable fun τ : ℝ =>
      (((whitK₁ (τ ^ 2 * y) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * τ * ((whitK₂ (τ ^ 2 * y) : ℝ) : ℂ)) * 𝓕 f τ := by
  obtain ⟨B₁, hB₁⟩ := whitK₁_iteratedDeriv_bounded 0
  obtain ⟨B₂, hB₂⟩ := whitK₂_iteratedDeriv_bounded 0
  simp only [iteratedDeriv_zero] at hB₁ hB₂
  have harg : Continuous fun τ : ℝ => τ ^ 2 * y := (continuous_id.pow 2).mul continuous_const
  have hk₁ : Continuous fun τ : ℝ => ((whitK₁ (τ ^ 2 * y) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_whitK₁.continuous.comp harg)
  have hk₂ : Continuous fun τ : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((whitK₂ (τ ^ 2 * y) : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_whitK₂.continuous.comp harg))
  have h₁ : Integrable fun τ : ℝ => ((whitK₁ (τ ^ 2 * y) : ℝ) : ℂ) * 𝓕 f τ :=
    (whit_fourier_integrable hf hc).bdd_mul hk₁.aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB₁ _)
  have h₂ : Integrable fun τ : ℝ =>
      2 * (Real.pi : ℂ) * Complex.I * ((whitK₂ (τ ^ 2 * y) : ℝ) : ℂ) * ((τ : ℂ) * 𝓕 f τ) := by
    refine (whit_tau_mul_fourier_integrable hf hc).bdd_mul (c := 2 * Real.pi * B₂) hk₂.aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left (hB₂ _) (by positivity)
  refine (h₁.add h₂).congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only [Pi.add_apply]
  ring

private theorem whitKer_mul_fourier_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (y : ℝ) : Integrable fun τ : ℝ => whitKer y τ * 𝓕 f τ :=
  whitKernel_integrable hf hc y

private theorem whit_exp_mul_fourier_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : ℝ) :
    Integrable fun τ : ℝ => Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ := by
  have hcont : Continuous fun τ : ℝ => Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).mul continuous_const)).mul
        continuous_const)
  refine (whit_fourier_integrable hf hc).bdd_mul (c := 1) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

private theorem whitRaw_sq_mul {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (x : ℝ) :
    (x : ℂ) * whitRaw f (x ^ 2) = (x : ℂ) * ((f x + f (-x)) / 2) + (f x - f (-x)) / 2 := by
  have hIp := whit_inversion hf hc x
  have hIm := whit_inversion hf hc (-x)
  have hintp := whit_exp_mul_fourier_integrable hf hc x
  have hintm := whit_exp_mul_fourier_integrable hf hc (-x)
  have hpt : ∀ τ : ℝ,
      (x : ℂ) * (whitKer (x ^ 2) τ * 𝓕 f τ) =
        ((x : ℂ) + 1) / 2 * (Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ) +
          ((x : ℂ) - 1) / 2 * (Complex.exp (((2 * Real.pi * τ * -x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ) := by
    intro τ
    unfold whitKer
    have hnn : (0 : ℝ) ≤ τ ^ 2 * x ^ 2 := by positivity
    have harg : 4 * Real.pi ^ 2 * (τ ^ 2 * x ^ 2) = (2 * Real.pi * τ * x) ^ 2 := by ring
    have e1 : whitK₁ (τ ^ 2 * x ^ 2) = Real.cos (2 * Real.pi * τ * x) := by
      rw [whitK₁_of_nonneg hnn, harg, whitC_sq]
    have e2 : 2 * Real.pi * τ * x * whitK₂ (τ ^ 2 * x ^ 2) = Real.sin (2 * Real.pi * τ * x) := by
      rw [whitK₂_of_nonneg hnn, harg, whitS_sq]
    set θ : ℂ := ((2 * Real.pi * τ * x : ℝ) : ℂ) with hθdef
    have hcos : ((whitK₁ (τ ^ 2 * x ^ 2) : ℝ) : ℂ) = Complex.cos θ := by
      rw [e1, Complex.ofReal_cos]
    have hsin : θ * ((whitK₂ (τ ^ 2 * x ^ 2) : ℝ) : ℂ) = Complex.sin θ := by
      rw [← Complex.ofReal_sin, ← e2, Complex.ofReal_mul]
    have hθ : θ = 2 * (Real.pi : ℂ) * (τ : ℂ) * (x : ℂ) := by
      rw [hθdef]
      push_cast
      ring
    have hneg : (((2 * Real.pi * τ * -x : ℝ) : ℂ)) = -θ := by
      rw [hθdef]
      push_cast
      ring
    rw [hneg]
    have h2c := Complex.two_cos (x := θ)
    have h2s := Complex.two_sin (x := θ)
    have hI2 := Complex.I_sq
    linear_combination (x : ℂ) * 𝓕 f τ * hcos + Complex.I * 𝓕 f τ * hsin -
      Complex.I * ((whitK₂ (τ ^ 2 * x ^ 2) : ℝ) : ℂ) * 𝓕 f τ * hθ + (x : ℂ) / 2 * 𝓕 f τ * h2c +
      Complex.I / 2 * 𝓕 f τ * h2s +
      (Complex.exp (-θ * Complex.I) - Complex.exp (θ * Complex.I)) / 2 * 𝓕 f τ * hI2
  have s1 : (x : ℂ) * whitRaw f (x ^ 2) = ∫ τ : ℝ, (x : ℂ) * (whitKer (x ^ 2) τ * 𝓕 f τ) := by
    rw [whitRaw_eq]
    exact (integral_const_mul _ _).symm
  have s2 : (∫ τ : ℝ, (x : ℂ) * (whitKer (x ^ 2) τ * 𝓕 f τ)) =
      ∫ τ : ℝ, (((x : ℂ) + 1) / 2 * (Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ) +
        ((x : ℂ) - 1) / 2 * (Complex.exp (((2 * Real.pi * τ * -x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ)) := by
    congr 1
    funext τ
    exact hpt τ
  have s3 : (∫ τ : ℝ, (((x : ℂ) + 1) / 2 * (Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ) +
        ((x : ℂ) - 1) / 2 * (Complex.exp (((2 * Real.pi * τ * -x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ))) =
      (∫ τ : ℝ, ((x : ℂ) + 1) / 2 * (Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ)) +
        ∫ τ : ℝ, ((x : ℂ) - 1) / 2 * (Complex.exp (((2 * Real.pi * τ * -x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ) :=
    integral_add (hintp.const_mul _) (hintm.const_mul _)
  have s4 : (∫ τ : ℝ, ((x : ℂ) + 1) / 2 * (Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ)) =
      ((x : ℂ) + 1) / 2 * ∫ τ : ℝ, Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ :=
    integral_const_mul _ _
  have s5 : (∫ τ : ℝ, ((x : ℂ) - 1) / 2 * (Complex.exp (((2 * Real.pi * τ * -x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ)) =
      ((x : ℂ) - 1) / 2 * ∫ τ : ℝ, Complex.exp (((2 * Real.pi * τ * -x : ℝ) : ℂ) * Complex.I) * 𝓕 f τ :=
    integral_const_mul _ _
  rw [s1, s2, s3, s4, s5, hIp, hIm]
  ring

private theorem whit_fourier_neg_of_even {f : ℝ → ℂ} (hev : ∀ x : ℝ, f (-x) = f x) (τ : ℝ) : 𝓕 f (-τ) = 𝓕 f τ := by
  have h1 : 𝓕⁻ f τ = 𝓕 f (-τ) := Real.fourierInv_eq_fourier_neg f τ
  have h2 : 𝓕⁻ f = 𝓕 fun x => f (-x) := Real.fourierInv_eq_fourier_comp_neg f
  have h3 : (fun x => f (-x)) = f := funext hev
  rw [← h1, h2, h3]

private theorem whit_integral_tau_mul_fourier_of_even {f : ℝ → ℂ} (hev : ∀ x : ℝ, f (-x) = f x) :
    ∫ τ : ℝ, (τ : ℂ) * 𝓕 f τ = 0 := by
  have h := integral_neg_eq_self (fun τ : ℝ => (τ : ℂ) * 𝓕 f τ) volume
  simp only [whit_fourier_neg_of_even hev, Complex.ofReal_neg, neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

private theorem whitRaw_zero_eq {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    whitRaw f 0 = f 0 + 2 * Real.pi * Complex.I * ∫ τ : ℝ, (τ : ℂ) * 𝓕 f τ := by
  have hpt : ∀ τ : ℝ, whitKer 0 τ * 𝓕 f τ = 𝓕 f τ + 2 * Real.pi * Complex.I * ((τ : ℂ) * 𝓕 f τ) := by
    intro τ
    unfold whitKer
    rw [mul_zero, whitK₁_of_nonneg le_rfl, whitK₂_of_nonneg le_rfl, mul_zero, whitC_zero, whitS_zero]
    push_cast
    ring
  have h0 := whit_inversion hf hc 0
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at h0
  have s1 : whitRaw f 0 = ∫ τ : ℝ, (𝓕 f τ + 2 * Real.pi * Complex.I * ((τ : ℂ) * 𝓕 f τ)) := by
    rw [whitRaw_eq]
    congr 1
    funext τ
    exact hpt τ
  have s2 : (∫ τ : ℝ, (𝓕 f τ + 2 * Real.pi * Complex.I * ((τ : ℂ) * 𝓕 f τ))) =
      (∫ τ : ℝ, 𝓕 f τ) + ∫ τ : ℝ, 2 * Real.pi * Complex.I * ((τ : ℂ) * 𝓕 f τ) :=
    integral_add (whit_fourier_integrable hf hc) ((whit_tau_mul_fourier_integrable hf hc).const_mul _)
  have s3 : (∫ τ : ℝ, 2 * Real.pi * Complex.I * ((τ : ℂ) * 𝓕 f τ)) =
      2 * Real.pi * Complex.I * ∫ τ : ℝ, (τ : ℂ) * 𝓕 f τ :=
    integral_const_mul _ _
  rw [s1, s2, s3, h0]

private theorem whitRaw_zero_of_even {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hev : ∀ x : ℝ, f (-x) = f x) : whitRaw f 0 = f 0 := by
  rw [whitRaw_zero_eq hf hc, whit_integral_tau_mul_fourier_of_even hev, mul_zero, add_zero]

private theorem whit_fourier_combination {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcg : HasCompactSupport g) (a b : ℂ) :
    𝓕 (fun x => a * f x + b * g x) = fun τ => a * 𝓕 f τ + b * 𝓕 g τ := by
  have hfun : (fun x => a * f x + b * g x) = ⇑(a • whitSchwartz f hf hcf + b • whitSchwartz g hg hcg) := by
    funext x
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, whitSchwartz_coe, smul_eq_mul]
  have e : 𝓕 (a • whitSchwartz f hf hcf + b • whitSchwartz g hg hcg) =
      a • 𝓕 (whitSchwartz f hf hcf) + b • 𝓕 (whitSchwartz g hg hcg) := by
    rw [fourier_add (E := SchwartzMap ℝ ℂ), fourier_smul (E := SchwartzMap ℝ ℂ), fourier_smul (E := SchwartzMap ℝ ℂ)]
  rw [hfun, ← SchwartzMap.fourier_coe, e]
  funext τ
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.fourier_coe, whitSchwartz_coe, smul_eq_mul]

private theorem whitRaw_combination {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcg : HasCompactSupport g) (a b : ℂ) (y : ℝ) :
    whitRaw (fun x => a * f x + b * g x) y = a * whitRaw f y + b * whitRaw g y := by
  have s1 : whitRaw (fun x => a * f x + b * g x) y =
      ∫ τ : ℝ, (a * (whitKer y τ * 𝓕 f τ) + b * (whitKer y τ * 𝓕 g τ)) := by
    rw [whitRaw_eq, whit_fourier_combination hf hcf hg hcg]
    congr 1
    funext τ
    ring
  have s2 : (∫ τ : ℝ, (a * (whitKer y τ * 𝓕 f τ) + b * (whitKer y τ * 𝓕 g τ))) =
      (∫ τ : ℝ, a * (whitKer y τ * 𝓕 f τ)) + ∫ τ : ℝ, b * (whitKer y τ * 𝓕 g τ) :=
    integral_add ((whitKer_mul_fourier_integrable hf hcf y).const_mul a)
      ((whitKer_mul_fourier_integrable hg hcg y).const_mul b)
  have s3 : (∫ τ : ℝ, a * (whitKer y τ * 𝓕 f τ)) = a * ∫ τ : ℝ, whitKer y τ * 𝓕 f τ := integral_const_mul _ _
  have s4 : (∫ τ : ℝ, b * (whitKer y τ * 𝓕 g τ)) = b * ∫ τ : ℝ, whitKer y τ * 𝓕 g τ := integral_const_mul _ _
  rw [s1, s2, s3, s4, whitRaw_eq, whitRaw_eq]

private theorem whitRaw_zero_fun (y : ℝ) : whitRaw (fun _ => (0 : ℂ)) y = 0 := by
  have h0 : 𝓕 (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
    funext τ
    rw [Real.fourier_real_eq]
    simp
  unfold whitRaw
  rw [h0]
  simp

private theorem whitW_linear : ∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
    HasCompactSupport g → ∀ a b : ℂ, whitW (fun x => a * f x + b * g x) = fun x => a * whitW f x + b * whitW g x := by
  intro f g hf hcf hg hcg a b
  funext y
  simp only [whitW, whitRaw_combination hf hcf hg hcg]
  ring

private theorem whitW_sq_of_even {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hev : ∀ x : ℝ, f (-x) = f x) : ∀ x : ℝ, whitW f (x ^ 2) = f x := by
  intro x
  rw [whitW, whitPsi_of_nonneg (by positivity), Complex.ofReal_one, one_mul]
  by_cases hx : x = 0
  · subst hx
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
    exact whitRaw_zero_of_even hf hc hev
  · have h := whitRaw_sq_mul hf hc x
    rw [hev] at h
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx
    apply mul_left_cancel₀ hx'
    rw [h]
    ring

private theorem whitW_sq_of_odd {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) : ∀ x : ℝ, (x : ℂ) * whitW f (x ^ 2) = f x := by
  intro x
  rw [whitW, whitPsi_of_nonneg (by positivity), Complex.ofReal_one, one_mul, whitRaw_sq_mul hf hc x, hodd]
  ring

open MeasureTheory Filter Topology
open scoped FourierTransform ContDiff

noncomputable section

namespace WhitneyEngine

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

section Families

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def dX (G : ℝ × Q → E) (z : ℝ × Q) : E := fderiv ℝ G z (1, 0)

private def dQ (G : ℝ × Q → E) (z : ℝ × Q) : Q →L[ℝ] E := (fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ ℝ Q)

private theorem contDiff_dX {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dX G) :=
  (contDiff_infty_iff_fderiv.1 hG).2.clm_apply contDiff_const

private theorem contDiff_dQ {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dQ G) :=
  (contDiff_infty_iff_fderiv.1 hG).2.clm_comp contDiff_const

private theorem
    hasCompactSupport_fderiv' {G : ℝ × Q → E} (hGc : HasCompactSupport G) : HasCompactSupport (fderiv ℝ G) :=
  IsCompact.of_isClosed_subset hGc (isClosed_tsupport _) (tsupport_fderiv_subset ℝ)

private theorem hasCompactSupport_dX {G : ℝ × Q → E} (hGc : HasCompactSupport G) : HasCompactSupport (dX G) := by
  refine (hasCompactSupport_fderiv' hGc).mono (Function.support_subset_iff'.2 fun z hz => ?_)
  rw [Function.mem_support, not_not] at hz
  simp [dX, hz]

private theorem hasCompactSupport_dQ {G : ℝ × Q → E} (hGc : HasCompactSupport G) : HasCompactSupport (dQ G) := by
  refine (hasCompactSupport_fderiv' hGc).mono (Function.support_subset_iff'.2 fun z hz => ?_)
  rw [Function.mem_support, not_not] at hz
  simp [dQ, hz]

omit [NormedSpace ℝ Q] [NormedSpace ℝ E] in

private theorem exists_xbound {G : ℝ × Q → E} (hGc : HasCompactSupport G) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : ℝ) (q : Q), R < |x| → G (x, q) = 0 := by
  obtain ⟨R, hR⟩ := hGc.isBounded.subset_closedBall 0
  refine ⟨max R 1, lt_max_of_lt_right one_pos, fun x q hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 : ‖((x, q) : ℝ × Q)‖ ≤ R := by simpa using hR hmem
  have h2 : |x| ≤ ‖((x, q) : ℝ × Q)‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_left _ _
  linarith [le_max_left R 1]

private theorem hasDerivAt_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (x : ℝ) (q : Q) :
    HasDerivAt (fun x => G (x, q)) (dX G (x, q)) x := by
  have hd : Differentiable ℝ G := (contDiff_infty_iff_fderiv.1 hG).1
  have h := (hd (x, q)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x q))
  simp [dX] at h
  exact h

private theorem deriv_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (q : Q) :
    deriv (fun x => G (x, q)) = fun x => dX G (x, q) :=
  funext fun x => (hasDerivAt_slice hG x q).deriv

private theorem
    differentiable_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (q : Q) : Differentiable ℝ fun x => G (x, q) :=
  fun x => (hasDerivAt_slice hG x q).differentiableAt

private theorem continuous_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (q : Q) : Continuous fun x => G (x, q) :=
  hG.continuous.comp (continuous_id.prodMk continuous_const)

private theorem contDiff_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (q : Q) : ContDiff ℝ ∞ fun x => G (x, q) :=
  hG.comp (contDiff_id.prodMk contDiff_const)

omit [NormedSpace ℝ Q] [NormedSpace ℝ E] in
private theorem hasCompactSupport_slice {G : ℝ × Q → E} (hGc : HasCompactSupport G) (q : Q) :
    HasCompactSupport fun x => G (x, q) := by
  obtain ⟨R, -, hR⟩ := exists_xbound hGc
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => hR x q ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
  · exact lt_of_lt_of_le hx (le_abs_self x)

private theorem integrable_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (q : Q) :
    Integrable fun x => G (x, q) :=
  (continuous_slice hG q).integrable_of_hasCompactSupport (hasCompactSupport_slice hGc q)

private theorem exists_integral_norm_le {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ q : Q, ∫ x, ‖G (x, q)‖ ≤ A := by
  obtain ⟨R, hR0, hR⟩ := exists_xbound hGc
  obtain ⟨C, hC⟩ := hG.continuous.bounded_above_of_compact_support hGc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C * (2 * R), by positivity, fun q => ?_⟩
  have hle : ∀ x, ‖G (x, q)‖ ≤ (Set.Icc (-R) R).indicator (fun _ => C) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hx]
      exact hC _
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      have : R < |x| := by
        rcases hx with hx | hx
        · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
        · exact lt_of_lt_of_le hx (le_abs_self x)
      rw [hR x q this, norm_zero]
  calc ∫ x, ‖G (x, q)‖ ≤ ∫ x, (Set.Icc (-R) R).indicator (fun _ => C) x :=
        integral_mono (integrable_slice hG hGc q).norm
          ((integrable_indicator_iff measurableSet_Icc).2
            (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (hC := enorm_ne_top)))
          hle
    _ = C * (2 * R) := by
        rw [integral_indicator_const C measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

end Families

section Fourier

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem norm_fourier_le {f : ℝ → E} (w : ℝ) : ‖𝓕 f w‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1 with x
  rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

omit [CompleteSpace E] in
private theorem continuous_fourier_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (q : Q) :
    Continuous (𝓕 (fun x => G (x, q))) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) (integrable_slice hG hGc q)

omit [CompleteSpace E] in

private theorem fourier_dX {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (q : Q) (τ : ℝ) :
    𝓕 (fun x => dX G (x, q)) τ = (2 * Real.pi * Complex.I * τ) • 𝓕 (fun x => G (x, q)) τ := by
  have h := Real.fourier_deriv (integrable_slice hG hGc q) (differentiable_slice hG q)
    (by rw [deriv_slice hG q]; exact integrable_slice (contDiff_dX hG) (hasCompactSupport_dX hGc) q)
  rw [deriv_slice hG q] at h
  exact congrFun h τ

omit [CompleteSpace E] in
private theorem fourier_dX_dX {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (q : Q) (τ : ℝ) :
    𝓕 (fun x => dX (dX G) (x, q)) τ = (2 * Real.pi * Complex.I * τ) ^ 2 • 𝓕 (fun x => G (x, q)) τ := by
  rw [fourier_dX (contDiff_dX hG) (hasCompactSupport_dX hGc), fourier_dX hG hGc, smul_smul, sq]

omit [CompleteSpace E] in
private theorem norm_fourier_dX_dX {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (q : Q) (τ : ℝ) :
    ‖𝓕 (fun x => dX (dX G) (x, q)) τ‖ = 4 * Real.pi ^ 2 * τ ^ 2 * ‖𝓕 (fun x => G (x, q)) τ‖ := by
  rw [fourier_dX_dX hG hGc, norm_smul, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  rw [show (2 * Real.pi * |τ|) ^ 2 = 4 * Real.pi ^ 2 * τ ^ 2 by rw [mul_pow, mul_pow, sq_abs]; ring]

private theorem fourier_decay (M : ℕ) :
    ∀ {G : ℝ × Q → E}, ContDiff ℝ ∞ G → HasCompactSupport G →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Q) (τ : ℝ), (1 + τ ^ 2) ^ M * ‖𝓕 (fun x => G (x, q)) τ‖ ≤ C := by
  induction M with
  | zero =>
      intro G hG hGc
      obtain ⟨A, hA0, hA⟩ := exists_integral_norm_le hG hGc
      exact ⟨A, hA0, fun q τ => by rw [pow_zero, one_mul]; exact (norm_fourier_le τ).trans (hA q)⟩
  | succ M ih =>
      intro G hG hGc
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih hG hGc
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih (contDiff_dX (contDiff_dX hG)) (hasCompactSupport_dX (hasCompactSupport_dX hGc))
      refine ⟨C₁ + C₂ / (4 * Real.pi ^ 2), by positivity, fun q τ => ?_⟩
      have hτ : 0 ≤ 1 + τ ^ 2 := by positivity
      have key : (1 + τ ^ 2) ^ (M + 1) * ‖𝓕 (fun x => G (x, q)) τ‖ =
          (1 + τ ^ 2) ^ M * ‖𝓕 (fun x => G (x, q)) τ‖ +
            (1 + τ ^ 2) ^ M * ‖𝓕 (fun x => dX (dX G) (x, q)) τ‖ / (4 * Real.pi ^ 2) := by
        rw [norm_fourier_dX_dX hG hGc]
        have hπ : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      rw [key]
      exact add_le_add (hC₁ q τ) (div_le_div_of_nonneg_right (hC₂ q τ) (by positivity))

private theorem fourier_decay' (M : ℕ) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Q) (τ : ℝ), ‖𝓕 (fun x => G (x, q)) τ‖ ≤ C * ((1 + τ ^ 2) ^ M)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := fourier_decay M hG hGc
  refine ⟨C, hC0, fun q τ => ?_⟩
  have hpos : 0 < (1 + τ ^ 2) ^ M := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact hC q τ

omit [CompleteSpace E] in

private theorem
    hasFDerivAt_fourier_slice {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (τ : ℝ) (q₀ : Q) :
    HasFDerivAt (fun q => 𝓕 (fun x => G (x, q)) τ) (𝓕 (fun x => dQ G (x, q₀)) τ) q₀ := by
  have hd : Differentiable ℝ G := (contDiff_infty_iff_fderiv.1 hG).1
  obtain ⟨R, -, hR⟩ := exists_xbound (hasCompactSupport_dQ hGc)
  obtain ⟨C, hC⟩ := (contDiff_dQ hG).continuous.bounded_above_of_compact_support (hasCompactSupport_dQ hGc)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have he : Continuous fun v : ℝ => ((Real.fourierChar (-(v * τ)) : Circle) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have eq1 : (fun q => 𝓕 (fun x => G (x, q)) τ) =
      fun q => ∫ v : ℝ, ((Real.fourierChar (-(v * τ)) : Circle) : ℂ) • G (v, q) := by
    funext q
    rw [Real.fourier_real_eq]
    simp_rw [Circle.smul_def]
  have eq2 : 𝓕 (fun x => dQ G (x, q₀)) τ = ∫ v : ℝ, ((Real.fourierChar (-(v * τ)) : Circle) : ℂ) • dQ G (v, q₀) := by
    rw [Real.fourier_real_eq]
    simp_rw [Circle.smul_def]
  rw [eq1, eq2]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (x₀ := q₀) (s := Set.univ)
    (F' := fun (q : Q) (v : ℝ) => ((Real.fourierChar (-(v * τ)) : Circle) : ℂ) • dQ G (v, q))
    (bound := (Set.Icc (-R) R).indicator fun _ => C) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun q => (he.smul (continuous_slice hG q)).aestronglyMeasurable
  · exact (he.smul (continuous_slice hG q₀)).integrable_of_hasCompactSupport (hasCompactSupport_slice hGc q₀).smul_left
  · exact (he.smul (continuous_slice (contDiff_dQ hG) q₀)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v q _ => ?_
    rw [norm_smul, Circle.norm_coe, one_mul]
    by_cases hv : v ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hv]
      exact hC _
    · rw [Set.indicator_of_notMem hv]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
      have : R < |v| := by
        rcases hv with hv | hv
        · exact lt_of_lt_of_le (by linarith) (neg_le_abs v)
        · exact lt_of_lt_of_le hv (le_abs_self v)
      rw [hR v q this, norm_zero]
  · exact (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (hC := enorm_ne_top))
  · refine Filter.Eventually.of_forall fun v q _ => ?_
    have h := ((hd (v, q)).hasFDerivAt.comp q (hasFDerivAt_prodMk_right v q)).const_smul
      ((Real.fourierChar (-(v * τ)) : Circle) : ℂ)
    simp [dQ] at h ⊢
    exact h

end Fourier

section Engine

private def KPoly (k : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ k ∧ ∀ j : ℕ, ∃ B : ℝ, ∃ N : ℕ, ∀ w : ℝ, |iteratedDeriv j k w| ≤ B * (1 + |w|) ^ N

private theorem KPoly.deriv {k : ℝ → ℝ} (hk : KPoly k) : KPoly (deriv k) := by
  refine ⟨(contDiff_infty_iff_deriv.1 hk.1).2, fun j => ?_⟩
  obtain ⟨B, N, h⟩ := hk.2 (j + 1)
  exact ⟨B, N, fun w => by rw [← iteratedDeriv_succ']; exact h w⟩

private theorem
    KPoly.bound₀ {k : ℝ → ℝ} (hk : KPoly k) : ∃ B : ℝ, ∃ N : ℕ, 0 ≤ B ∧ ∀ w : ℝ, |k w| ≤ B * (1 + |w|) ^ N := by
  obtain ⟨B, N, h⟩ := hk.2 0
  refine ⟨max B 0, N, le_max_right _ _, fun w => ?_⟩
  have := h w
  rw [iteratedDeriv_zero] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

private theorem KPoly.continuous {k : ℝ → ℝ} (hk : KPoly k) : Continuous k := hk.1.continuous

private theorem KPoly.hasDerivAt {k : ℝ → ℝ} (hk : KPoly k) (w : ℝ) : HasDerivAt k (_root_.deriv k w) w :=
  ((contDiff_infty_iff_deriv.1 hk.1).1 w).hasDerivAt

private theorem one_add_abs_pow_le (τ y : ℝ) (N : ℕ) : (1 + |τ ^ 2 * y|) ^ N ≤ (1 + |y|) ^ N * (1 + τ ^ 2) ^ N :=
  calc (1 + |τ ^ 2 * y|) ^ N = (1 + τ ^ 2 * |y|) ^ N := by rw [abs_mul, abs_of_nonneg (sq_nonneg τ)]
    _ ≤ ((1 + |y|) * (1 + τ ^ 2)) ^ N :=
        pow_le_pow_left₀ (by positivity)
          (by nlinarith [sq_nonneg τ, abs_nonneg y, mul_nonneg (sq_nonneg τ) (abs_nonneg y)]) N
    _ = (1 + |y|) ^ N * (1 + τ ^ 2) ^ N := mul_pow _ _ _

private theorem kernel_est {k : ℝ → ℝ} {B : ℝ} {N : ℕ} (hB : 0 ≤ B) (hk : ∀ w, |k w| ≤ B * (1 + |w|) ^ N) {Y y : ℝ}
    (hy : |y| ≤ Y) (τ : ℝ) : |k (τ ^ 2 * y)| ≤ B * (1 + Y) ^ N * (1 + τ ^ 2) ^ N :=
  calc |k (τ ^ 2 * y)| ≤ B * (1 + |τ ^ 2 * y|) ^ N := hk _
    _ ≤ B * ((1 + |y|) ^ N * (1 + τ ^ 2) ^ N) := mul_le_mul_of_nonneg_left (one_add_abs_pow_le τ y N) hB
    _ ≤ B * ((1 + Y) ^ N * (1 + τ ^ 2) ^ N) := by gcongr
    _ = B * (1 + Y) ^ N * (1 + τ ^ 2) ^ N := by ring

omit [NormedSpace ℝ Q] in
private theorem abs_fst_le_of_mem_ball {z₀ z : ℝ × Q} (hz : z ∈ Metric.ball z₀ 1) : |z.1| ≤ |z₀.1| + 1 := by
  have h1 : ‖z - z₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have h2 : |z.1 - z₀.1| ≤ ‖z - z₀‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have := abs_sub_abs_le_abs_sub z.1 z₀.1
  linarith

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private def Phi (k : ℝ → ℝ) (G : ℝ × Q → E) (z : ℝ × Q) : E := ∫ τ : ℝ, k (τ ^ 2 * z.1) • 𝓕 (fun x => G (x, z.2)) τ

private def Fint (k : ℝ → ℝ) (G : ℝ × Q → E) (z : ℝ × Q) (τ : ℝ) : E := k (τ ^ 2 * z.1) • 𝓕 (fun x => G (x, z.2)) τ

private def cK (k : ℝ → ℝ) (z : ℝ × Q) (τ : ℝ) : ℝ × Q →L[ℝ] ℝ :=
  (τ ^ 2 * _root_.deriv k (τ ^ 2 * z.1)) • ContinuousLinearMap.fst ℝ ℝ Q

private def Fder (k : ℝ → ℝ) (G : ℝ × Q → E) (z : ℝ × Q) (τ : ℝ) : ℝ × Q →L[ℝ] E :=
  k (τ ^ 2 * z.1) • (𝓕 (fun x => dQ G (x, z.2)) τ).comp (ContinuousLinearMap.snd ℝ ℝ Q) +
    (cK k z τ).smulRight (𝓕 (fun x => G (x, z.2)) τ)

private def G₂ (G : ℝ × Q → E) (z : ℝ × Q) : E := (-(1 / (4 * Real.pi ^ 2)) : ℝ) • dX (dX G) z

omit [CompleteSpace E] in
private theorem contDiff_G₂ {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (G₂ G) := by
  show ContDiff ℝ ∞ fun z => (-(1 / (4 * Real.pi ^ 2)) : ℝ) • dX (dX G) z
  exact (contDiff_dX (contDiff_dX hG)).const_smul (-(1 / (4 * Real.pi ^ 2)) : ℝ)

omit [CompleteSpace E] in
private theorem hasCompactSupport_G₂ {G : ℝ × Q → E} (hGc : HasCompactSupport G) : HasCompactSupport (G₂ G) :=
  (hasCompactSupport_dX (hasCompactSupport_dX hGc)).smul_left

omit [CompleteSpace E] in

private theorem fourier_real_smul (r : ℝ) (g : ℝ → E) (τ : ℝ) : 𝓕 (fun x => r • g x) τ = r • 𝓕 g τ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← Complex.coe_smul, ← integral_smul]
  congr 1 with v
  rw [Circle.smul_def, Circle.smul_def, ← Complex.coe_smul, smul_smul, smul_smul, mul_comm]

omit [CompleteSpace E] in
private theorem fourier_G₂ {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (q : Q) (τ : ℝ) :
    𝓕 (fun x => G₂ G (x, q)) τ = (τ ^ 2) • 𝓕 (fun x => G (x, q)) τ := by
  unfold G₂
  rw [fourier_real_smul, fourier_dX_dX hG hGc, ← Complex.coe_smul, smul_smul, ← Complex.coe_smul]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h4 : (4 * (Real.pi : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)
  have hsq : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ 2 = -(4 * (Real.pi : ℂ) ^ 2 * (τ : ℂ) ^ 2) := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) = (2 * Real.pi * τ : ℂ) * Complex.I by ring, mul_pow,
      Complex.I_sq]
    ring
  rw [hsq]
  push_cast
  linear_combination ((τ : ℂ) ^ 2) * one_div_mul_cancel h4

private def PhiDeriv (k : ℝ → ℝ) (G : ℝ × Q → E) (z : ℝ × Q) : ℝ × Q →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ Q).smulRight (Phi (_root_.deriv k) (G₂ G) z) +
    (Phi k (dQ G) z).comp (ContinuousLinearMap.snd ℝ ℝ Q)

omit [CompleteSpace E] in
private theorem hasFDerivAt_Fint {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (τ : ℝ) (z : ℝ × Q) :
    HasFDerivAt (fun z => Fint k G z τ) (Fder k G z τ) z := by
  have hl : HasFDerivAt (fun z : ℝ × Q => τ ^ 2 * z.1) ((τ ^ 2) • ContinuousLinearMap.fst ℝ ℝ Q) z :=
    hasFDerivAt_fst.const_mul (τ ^ 2)
  have h1 : HasFDerivAt (fun z : ℝ × Q => k (τ ^ 2 * z.1)) (cK k z τ) z := by
    refine ((hk.hasDerivAt (τ ^ 2 * z.1)).comp_hasFDerivAt z hl).congr_fderiv ?_
    rw [cK, smul_smul, mul_comm]
  have h2 : HasFDerivAt (fun z : ℝ × Q => 𝓕 (fun x => G (x, z.2)) τ)
      ((𝓕 (fun x => dQ G (x, z.2)) τ).comp (ContinuousLinearMap.snd ℝ ℝ Q)) z :=
    (hasFDerivAt_fourier_slice hG hGc τ z.2).comp z hasFDerivAt_snd
  exact h1.fun_smul h2

omit [CompleteSpace E] in
private theorem
    continuous_Fint {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (z : ℝ × Q) : Continuous (Fint k G z) :=
  (hk.continuous.comp (by fun_prop)).smul (continuous_fourier_slice hG hGc z.2)

private theorem continuous_cK {k : ℝ → ℝ} (hk : KPoly k) (z : ℝ × Q) : Continuous (cK k z) :=
  ((continuous_pow 2).mul (hk.deriv.continuous.comp (by fun_prop))).smul continuous_const

omit [CompleteSpace E] in
private theorem
    continuous_Fder {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (z : ℝ × Q) : Continuous (Fder k G z) := by
  refine Continuous.add ?_ ?_
  · exact (hk.continuous.comp (by fun_prop)).smul
      ((continuous_fourier_slice (contDiff_dQ hG) (hasCompactSupport_dQ hGc) z.2).clm_comp continuous_const)
  · exact ((ContinuousLinearMap.smulRightL ℝ (ℝ × Q) E).continuous₂ :).comp
      ((continuous_cK hk z).prodMk (continuous_fourier_slice hG hGc z.2))

private theorem integrable_kernel_smul {k : ℝ → ℝ} (hkc : Continuous k) {B : ℝ} {N : ℕ} (hB : 0 ≤ B)
    (hk : ∀ w, |k w| ≤ B * (1 + |w|) ^ N) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (z : ℝ × Q) : Integrable fun τ => k (τ ^ 2 * z.1) • 𝓕 (fun x => G (x, z.2)) τ := by
  obtain ⟨C, hC0, hC⟩ := fourier_decay' (N + 1) hG hGc
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (B * (1 + |z.1|) ^ N * C))
    ((hkc.comp (by fun_prop)).smul (continuous_fourier_slice hG hGc z.2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  have hτ : 0 < 1 + τ ^ 2 := by positivity
  rw [norm_smul, Real.norm_eq_abs]
  calc |k (τ ^ 2 * z.1)| * ‖𝓕 (fun x => G (x, z.2)) τ‖
      ≤ (B * (1 + |z.1|) ^ N * (1 + τ ^ 2) ^ N) * (C * ((1 + τ ^ 2) ^ (N + 1))⁻¹) :=
        mul_le_mul (kernel_est hB hk le_rfl τ) (hC z.2 τ) (norm_nonneg _) (by positivity)
    _ = B * (1 + |z.1|) ^ N * C * (1 + τ ^ 2)⁻¹ := by
        rw [pow_succ]
        field_simp
        ring

private theorem
    integrable_Fint {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (z : ℝ × Q) : Integrable (Fint k G z) := by
  obtain ⟨B, N, hB, hkB⟩ := hk.bound₀
  exact integrable_kernel_smul hk.continuous hB hkB hG hGc z

private theorem integrable_weighted {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (z : ℝ × Q) :
    Integrable fun τ => (τ ^ 2 * _root_.deriv k (τ ^ 2 * z.1)) • 𝓕 (fun x => G (x, z.2)) τ := by
  have h := integrable_kernel_smul hk.deriv.continuous (hk.deriv.bound₀.choose_spec.choose_spec.1)
    (hk.deriv.bound₀.choose_spec.choose_spec.2) (contDiff_G₂ hG) (hasCompactSupport_G₂ hGc) z
  refine (h.congr (Filter.Eventually.of_forall fun τ => ?_))
  show _root_.deriv k (τ ^ 2 * z.1) • 𝓕 (fun x => G₂ G (x, z.2)) τ = _
  rw [fourier_G₂ hG hGc, smul_smul, mul_comm]

private theorem
    exists_Fder_bound {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (z₀ : ℝ × Q) : ∃ K : ℝ, ∀ z ∈ Metric.ball z₀ 1, ∀ τ : ℝ, ‖Fder k G z τ‖ ≤ K * (1 + τ ^ 2)⁻¹ := by
  obtain ⟨B₀, N₀, hB₀, hk₀⟩ := hk.bound₀
  obtain ⟨B₁, N₁, hB₁, hk₁⟩ := hk.deriv.bound₀
  obtain ⟨C₀, hC₀0, hC₀⟩ := fourier_decay' (N₀ + 1) (contDiff_dQ hG) (hasCompactSupport_dQ hGc)
  obtain ⟨C₁, hC₁0, hC₁⟩ := fourier_decay' (N₁ + 2) hG hGc
  set Y : ℝ := |z₀.1| + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  refine ⟨B₀ * (1 + Y) ^ N₀ * C₀ + B₁ * (1 + Y) ^ N₁ * C₁, fun z hz τ => ?_⟩
  have hz1 : |z.1| ≤ Y := abs_fst_le_of_mem_ball hz
  have hτ : 0 < 1 + τ ^ 2 := by positivity
  have h1 : ‖k (τ ^ 2 * z.1) • (𝓕 (fun x => dQ G (x, z.2)) τ).comp (ContinuousLinearMap.snd ℝ ℝ Q)‖ ≤
      B₀ * (1 + Y) ^ N₀ * C₀ * (1 + τ ^ 2)⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |k (τ ^ 2 * z.1)| * ‖(𝓕 (fun x => dQ G (x, z.2)) τ).comp (ContinuousLinearMap.snd ℝ ℝ Q)‖
        ≤ (B₀ * (1 + Y) ^ N₀ * (1 + τ ^ 2) ^ N₀) * (C₀ * ((1 + τ ^ 2) ^ (N₀ + 1))⁻¹) := by
          refine mul_le_mul (kernel_est hB₀ hk₀ hz1 τ) ?_ (norm_nonneg _) (by positivity)
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          calc ‖𝓕 (fun x => dQ G (x, z.2)) τ‖ * ‖ContinuousLinearMap.snd ℝ ℝ Q‖
              ≤ ‖𝓕 (fun x => dQ G (x, z.2)) τ‖ * 1 :=
                mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ..) (norm_nonneg _)
            _ ≤ C₀ * ((1 + τ ^ 2) ^ (N₀ + 1))⁻¹ := by rw [mul_one]; exact hC₀ z.2 τ
      _ = B₀ * (1 + Y) ^ N₀ * C₀ * (1 + τ ^ 2)⁻¹ := by
          rw [pow_succ]
          field_simp
          ring
  have h2 : ‖(cK k z τ).smulRight (𝓕 (fun x => G (x, z.2)) τ)‖ ≤ B₁ * (1 + Y) ^ N₁ * C₁ * (1 + τ ^ 2)⁻¹ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have hc : ‖cK k z τ‖ ≤ τ ^ 2 * |_root_.deriv k (τ ^ 2 * z.1)| := by
      rw [cK, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg τ)]
      calc τ ^ 2 * |_root_.deriv k (τ ^ 2 * z.1)| * ‖ContinuousLinearMap.fst ℝ ℝ Q‖
          ≤ τ ^ 2 * |_root_.deriv k (τ ^ 2 * z.1)| * 1 := by
            gcongr
            exact ContinuousLinearMap.norm_fst_le ..
        _ = _ := by rw [mul_one]
    calc ‖cK k z τ‖ * ‖𝓕 (fun x => G (x, z.2)) τ‖
        ≤ (τ ^ 2 * |_root_.deriv k (τ ^ 2 * z.1)|) * (C₁ * ((1 + τ ^ 2) ^ (N₁ + 2))⁻¹) :=
          mul_le_mul hc (hC₁ z.2 τ) (norm_nonneg _) (by positivity)
      _ ≤ ((1 + τ ^ 2) * (B₁ * (1 + Y) ^ N₁ * (1 + τ ^ 2) ^ N₁)) * (C₁ * ((1 + τ ^ 2) ^ (N₁ + 2))⁻¹) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul (by nlinarith [sq_nonneg τ]) (kernel_est hB₁ hk₁ hz1 τ) (abs_nonneg _) (by positivity)
      _ = B₁ * (1 + Y) ^ N₁ * C₁ * (1 + τ ^ 2)⁻¹ := by
          rw [pow_succ, pow_succ]
          field_simp
          ring
  calc ‖Fder k G z τ‖ ≤ ‖k (τ ^ 2 * z.1) • (𝓕 (fun x => dQ G (x, z.2)) τ).comp (ContinuousLinearMap.snd ℝ ℝ Q)‖ +
        ‖(cK k z τ).smulRight (𝓕 (fun x => G (x, z.2)) τ)‖ := norm_add_le _ _
    _ ≤ B₀ * (1 + Y) ^ N₀ * C₀ * (1 + τ ^ 2)⁻¹ + B₁ * (1 + Y) ^ N₁ * C₁ * (1 + τ ^ 2)⁻¹ := add_le_add h1 h2
    _ = (B₀ * (1 + Y) ^ N₀ * C₀ + B₁ * (1 + Y) ^ N₁ * C₁) * (1 + τ ^ 2)⁻¹ := by ring

private theorem
    integral_Fder {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (z : ℝ × Q) : ∫ τ, Fder k G z τ = PhiDeriv k G z := by
  set L₁ : E →L[ℝ] (ℝ × Q →L[ℝ] E) := ContinuousLinearMap.smulRightL ℝ (ℝ × Q) E (ContinuousLinearMap.fst ℝ ℝ Q)
    with hL₁
  set L₂ : (Q →L[ℝ] E) →L[ℝ] (ℝ × Q →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ (ℝ × Q) Q E).flip (ContinuousLinearMap.snd ℝ ℝ Q) with hL₂
  have iA : Integrable fun τ => k (τ ^ 2 * z.1) • 𝓕 (fun x => dQ G (x, z.2)) τ :=
    integrable_Fint hk (contDiff_dQ hG) (hasCompactSupport_dQ hGc) z
  have iB := integrable_weighted hk hG hGc z
  have eA : ∀ τ, k (τ ^ 2 * z.1) • (𝓕 (fun x => dQ G (x, z.2)) τ).comp (ContinuousLinearMap.snd ℝ ℝ Q) =
      L₂ (k (τ ^ 2 * z.1) • 𝓕 (fun x => dQ G (x, z.2)) τ) := by
    intro τ
    rw [hL₂, map_smul]
    rfl
  have hL₁v : ∀ v : E, L₁ v = (ContinuousLinearMap.fst ℝ ℝ Q).smulRight v := fun v => rfl
  have eB : ∀ τ, (cK k z τ).smulRight (𝓕 (fun x => G (x, z.2)) τ) =
      L₁ ((τ ^ 2 * _root_.deriv k (τ ^ 2 * z.1)) • 𝓕 (fun x => G (x, z.2)) τ) := by
    intro τ
    rw [hL₁v, cK]
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      smul_smul, smul_eq_mul]
    rw [mul_comm]
  have eqB : ∫ τ, (τ ^ 2 * _root_.deriv k (τ ^ 2 * z.1)) • 𝓕 (fun x => G (x, z.2)) τ =
      Phi (_root_.deriv k) (G₂ G) z := by
    unfold Phi
    congr 1 with τ
    rw [fourier_G₂ hG hGc, smul_smul, mul_comm]
  unfold Fder
  rw [integral_add ((L₂.integrable_comp iA).congr (Filter.Eventually.of_forall fun τ => (eA τ).symm))
    ((L₁.integrable_comp iB).congr (Filter.Eventually.of_forall fun τ => (eB τ).symm))]
  simp_rw [eA, eB]
  rw [L₂.integral_comp_comm iA, L₁.integral_comp_comm iB, eqB, PhiDeriv, add_comm, hL₁, hL₂]
  rfl

private theorem
    hasFDerivAt_Phi {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (z₀ : ℝ × Q) : HasFDerivAt (Phi k G) (PhiDeriv k G z₀) z₀ := by
  obtain ⟨K, hK⟩ := exists_Fder_bound hk hG hGc z₀
  rw [← integral_Fder hk hG hGc z₀]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (x₀ := z₀) (s := Metric.ball z₀ 1)
    (F := Fint k G) (F' := Fder k G) (bound := fun τ => K * (1 + τ ^ 2)⁻¹) (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (continuous_Fint hk hG hGc z).aestronglyMeasurable)
    (integrable_Fint hk hG hGc z₀) (continuous_Fder hk hG hGc z₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ z hz => hK z hz τ) (integrable_inv_one_add_sq.const_mul K)
    (Filter.Eventually.of_forall fun τ z _ => hasFDerivAt_Fint hk hG hGc τ z)

private theorem contDiff_Phi_nat (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {k : ℝ → ℝ}, KPoly k →
      ∀ {G : ℝ × Q → E}, ContDiff ℝ ∞ G → HasCompactSupport G → ContDiff ℝ n (Phi k G) := by
  induction n with
  | zero =>
      intro E _ _ _ k hk G hG hGc
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z => (hasFDerivAt_Phi hk hG hGc z).continuousAt)
  | succ n ih =>
      intro E _ _ _ k hk G hG hGc
      suffices h : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (Phi k G) by exact_mod_cast h
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨PhiDeriv k G, ?_, fun z => hasFDerivAt_Phi hk hG hGc z⟩
      have h1 : ContDiff ℝ n (Phi (_root_.deriv k) (G₂ G)) := ih hk.deriv (contDiff_G₂ hG) (hasCompactSupport_G₂ hGc)
      have h2 : ContDiff ℝ n (Phi k (dQ G)) := ih hk (contDiff_dQ hG) (hasCompactSupport_dQ hGc)
      exact (contDiff_const.smulRight h1).add (h2.clm_comp contDiff_const)

private theorem
    contDiff_Phi {k : ℝ → ℝ} (hk : KPoly k) {G : ℝ × Q → E} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    ContDiff ℝ ∞ (Phi k G) :=
  contDiff_infty.2 fun n => contDiff_Phi_nat n hk hG hGc

end Engine

section Layer

private def Wraw (K₁ K₂ : ℝ → ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ τ : ℝ, (((K₁ (τ ^ 2 * y) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * τ * ((K₂ (τ ^ 2 * y) : ℝ) : ℂ)) * 𝓕 f τ

private def Wop (K₁ K₂ ψ : ℝ → ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ := ((ψ y : ℝ) : ℂ) * Wraw K₁ K₂ f y

variable {K₁ K₂ ψ : ℝ → ℝ}

private theorem Wraw_slice (hK₁ : KPoly K₁) (hK₂ : KPoly K₂) {H : ℝ × Q → ℂ} (hH : ContDiff ℝ ∞ H)
    (hHc : HasCompactSupport H) (y : ℝ) (q : Q) :
    Wraw K₁ K₂ (fun x => H (x, q)) y = Phi K₁ H (y, q) + Phi K₂ (dX H) (y, q) := by
  have i1 := integrable_Fint hK₁ hH hHc (y, q)
  have i2 := integrable_Fint hK₂ (contDiff_dX hH) (hasCompactSupport_dX hHc) (y, q)
  unfold Fint at i1 i2
  unfold Wraw Phi
  dsimp only at i1 i2 ⊢
  rw [← integral_add i1 i2]
  congr 1 with τ
  rw [fourier_dX hH hHc, ← Complex.coe_smul, ← Complex.coe_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

private theorem Wop_family_eq (hK₁ : KPoly K₁) (hK₂ : KPoly K₂) {H : ℝ × Q → ℂ} (hH : ContDiff ℝ ∞ H)
    (hHc : HasCompactSupport H) :
    (fun z : ℝ × Q => Wop K₁ K₂ ψ (fun x => H (x, z.2)) z.1) =
      fun z => ((ψ z.1 : ℝ) : ℂ) * (Phi K₁ H z + Phi K₂ (dX H) z) := by
  funext z
  rw [Wop, Wraw_slice hK₁ hK₂ hH hHc]

private theorem contDiff_Wop_family (hK₁ : KPoly K₁) (hK₂ : KPoly K₂) (hψ : ContDiff ℝ ∞ ψ) {H : ℝ × Q → ℂ}
    (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    ContDiff ℝ ∞ fun z : ℝ × Q => Wop K₁ K₂ ψ (fun x => H (x, z.2)) z.1 := by
  rw [Wop_family_eq hK₁ hK₂ hH hHc]
  refine ContDiff.mul ?_ ((contDiff_Phi hK₁ hH hHc).add (contDiff_Phi hK₂ (contDiff_dX hH) (hasCompactSupport_dX hHc)))
  exact Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_fst)

omit [NormedSpace ℝ Q] in

private theorem slice_eq_zero {H : ℝ × Q → ℂ} {q : Q} (hq : q ∉ Prod.snd '' tsupport H) :
    (fun x => H (x, q)) = fun _ => 0 := by
  funext x
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  exact hq ⟨(x, q), hx, rfl⟩

private theorem Wraw_zero_fun (y : ℝ) : Wraw K₁ K₂ (fun _ : ℝ => (0 : ℂ)) y = 0 := by
  have h0 : 𝓕 (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
    funext τ
    rw [Real.fourier_real_eq]
    simp
  unfold Wraw
  rw [h0]
  simp

private theorem hasCompactSupport_Wop_family (hψ0 : ∀ y : ℝ, y ≤ -1 → ψ y = 0)
    (hhalf : ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∀ x : ℝ, 0 < x → g x = 0 → g (-x) = 0 → Wraw K₁ K₂ g (x ^ 2) = 0)
    {H : ℝ × Q → ℂ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    HasCompactSupport fun z : ℝ × Q => Wop K₁ K₂ ψ (fun x => H (x, z.2)) z.1 := by
  obtain ⟨R, hR0, hR⟩ := exists_xbound hHc
  have hKq : IsCompact (Prod.snd '' tsupport H) := hHc.image continuous_snd
  have hsub : (Function.support fun z : ℝ × Q => Wop K₁ K₂ ψ (fun x => H (x, z.2)) z.1) ⊆
      Set.Icc (-1) (R ^ 2) ×ˢ (Prod.snd '' tsupport H) := by
    intro z hz
    rw [Function.mem_support] at hz
    refine Set.mem_prod.2 ⟨?_, ?_⟩
    · by_contra hy
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
      apply hz
      rcases hy with hy | hy
      · rw [Wop, hψ0 z.1 hy.le, Complex.ofReal_zero, zero_mul]
      · have hz0 : 0 < z.1 := lt_of_le_of_lt (sq_nonneg R) hy
        have hx : R < Real.sqrt z.1 := by
          calc R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hR0.le).symm
            _ < Real.sqrt z.1 := Real.sqrt_lt_sqrt (sq_nonneg R) hy
        have hxpos : 0 < Real.sqrt z.1 := Real.sqrt_pos.2 hz0
        have h1 : H (Real.sqrt z.1, z.2) = 0 := hR _ _ (by rwa [abs_of_pos hxpos])
        have h2 : H (-Real.sqrt z.1, z.2) = 0 := hR _ _ (by rwa [abs_neg, abs_of_pos hxpos])
        have h0 := hhalf (fun x => H (x, z.2)) (contDiff_slice hH z.2) (hasCompactSupport_slice hHc z.2) _ hxpos h1 h2
        rw [Real.sq_sqrt hz0.le] at h0
        rw [Wop, h0, mul_zero]
    · by_contra hq
      apply hz
      rw [Wop, slice_eq_zero hq, Wraw_zero_fun, mul_zero]
  exact IsCompact.of_isClosed_subset (isCompact_Icc.prod hKq) (isClosed_tsupport _)
    (closure_minimal hsub (isClosed_Icc.prod hKq.isClosed))

private theorem contDiff_Wop (hK₁ : KPoly K₁) (hK₂ : KPoly K₂) (hψ : ContDiff ℝ ∞ ψ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : ContDiff ℝ ∞ (Wop K₁ K₂ ψ f) := by
  have hH : ContDiff ℝ ∞ fun z : ℝ × PUnit => f z.1 := hf.comp contDiff_fst
  have hHc : HasCompactSupport fun z : ℝ × PUnit => f z.1 := hfc.comp_homeomorph (Homeomorph.prodPUnit ℝ)
  exact (contDiff_Wop_family (Q := PUnit) hK₁ hK₂ hψ hH hHc).comp
    (contDiff_id.prodMk (contDiff_const (c := (PUnit.unit : PUnit))))

private theorem hasCompactSupport_Wop (hψ0 : ∀ y : ℝ, y ≤ -1 → ψ y = 0)
    (hhalf : ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∀ x : ℝ, 0 < x → g x = 0 → g (-x) = 0 → Wraw K₁ K₂ g (x ^ 2) = 0)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) : HasCompactSupport (Wop K₁ K₂ ψ f) := by
  have hH : ContDiff ℝ ∞ fun z : ℝ × PUnit => f z.1 := hf.comp contDiff_fst
  have hHc : HasCompactSupport fun z : ℝ × PUnit => f z.1 := hfc.comp_homeomorph (Homeomorph.prodPUnit ℝ)
  have e : Wop K₁ K₂ ψ f =
      (fun z : ℝ × PUnit => Wop K₁ K₂ ψ (fun x => f (x, z.2).1) z.1) ∘ (Homeomorph.prodPUnit ℝ).symm := rfl
  rw [e]
  exact (hasCompactSupport_Wop_family (Q := PUnit) hψ0 hhalf hH hHc).comp_homeomorph _

end Layer

end WhitneyEngine

end

noncomputable section

namespace WhitneyEngine

open scoped ContDiff

private theorem kpoly₁ : KPoly whitK₁ := ⟨contDiff_whitK₁, whitK₁_iteratedDeriv_polyGrowth⟩

private theorem kpoly₂ : KPoly whitK₂ := ⟨contDiff_whitK₂, whitK₂_iteratedDeriv_polyGrowth⟩

private theorem whitRaw_eq_Wraw : whitRaw = Wraw whitK₁ whitK₂ := rfl

private theorem whitW_eq_Wop : whitW = Wop whitK₁ whitK₂ whitPsi := rfl

private theorem Wraw_sq_eq_zero (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (x : ℝ) (hx : 0 < x)
    (h1 : g x = 0) (h2 : g (-x) = 0) : Wraw whitK₁ whitK₂ g (x ^ 2) = 0 := by
  have h := whitRaw_sq_mul hg hgc x
  rw [h1, h2, whitRaw_eq_Wraw] at h
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have h0 : (x : ℂ) * Wraw whitK₁ whitK₂ g (x ^ 2) = 0 := by rw [h]; ring
  exact (mul_eq_zero.1 h0).resolve_left hx'

private theorem whitPsi_zero_of_le : ∀ y : ℝ, y ≤ -1 → whitPsi y = 0 := fun _ hy => whitPsi_of_le hy

end WhitneyEngine

end

open WhitneyEngine in

theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ W : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, W (fun x => a * f x + b * g x) = fun x => a * W f x + b * W g x) ∧
      (∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ContDiff ℝ (⊤ : ℕ∞) (W f) ∧ HasCompactSupport (W f) ∧
        ((∀ x : ℝ, f (-x) = f x) → ∀ x : ℝ, W f (x ^ 2) = f x) ∧
        ((∀ x : ℝ, f (-x) = -f x) → ∀ x : ℝ, (x : ℂ) * W f (x ^ 2) = f x)) ∧
      ∀ H : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) ∧
          HasCompactSupport (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) := by
  refine ⟨whitW, whitW_linear, fun f hf hc => ⟨?_, ?_, whitW_sq_of_even hf hc, whitW_sq_of_odd hf hc⟩,
    fun H hH hHc => ⟨?_, ?_⟩⟩
  · rw [whitW_eq_Wop]
    exact contDiff_Wop kpoly₁ kpoly₂ contDiff_whitPsi hf hc
  · rw [whitW_eq_Wop]
    exact hasCompactSupport_Wop whitPsi_zero_of_le Wraw_sq_eq_zero hf hc
  · rw [whitW_eq_Wop]
    exact contDiff_Wop_family kpoly₁ kpoly₂ contDiff_whitPsi hH hHc
  · rw [whitW_eq_Wop]
    exact hasCompactSupport_Wop_family whitPsi_zero_of_le Wraw_sq_eq_zero hH hHc

end S_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
end P2MW
export P2MW.S_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd (solution)
