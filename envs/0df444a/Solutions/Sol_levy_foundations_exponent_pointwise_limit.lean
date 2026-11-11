-- Prove2me | solution 1 for levy_foundations_exponent_pointwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T18:00:42.173332+00:00
-- url     : https://prove2.me/submissions/6609bf8c-0b0d-46a2-af8b-8ad2d597b830

import Mathlib
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_converse
import Theorems.Thm_levy_foundations_exponentContinuous

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped NNReal ENNReal

namespace LevyLimitAux


open LevyFoundations in
theorem comp_measurable (ξ : ℝ) : Measurable (fun x : ℝ => compensatedIntegrand ξ x) := by
  unfold compensatedIntegrand
  refine Measurable.sub (Measurable.sub (by fun_prop) measurable_const) ?_
  refine Measurable.mul (by fun_prop) ?_
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const

theorem taylor_bound (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I‖ ≤ 3 * u ^ 2 := by
  have hn : ‖Complex.exp ((u : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I u
  have hI : ‖(u : ℂ) * Complex.I‖ = |u| := by simp
  by_cases h : |u| ≤ 1
  · have := Complex.norm_exp_sub_one_sub_id_le (x := (u : ℂ) * Complex.I) (by rw [hI]; exact h)
    rw [hI, sq_abs] at this
    nlinarith [sq_nonneg u]
  · rw [not_le] at h
    calc ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I‖
        ≤ ‖Complex.exp ((u : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 2 + |u| := by rw [hn, hI]; norm_num
      _ ≤ 3 * u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]

open LevyFoundations in
theorem comp_bound (ξ x : ℝ) :
    ‖compensatedIntegrand ξ x‖ ≤ (3 * ξ ^ 2 + 2) * min 1 (x ^ 2) := by
  unfold compensatedIntegrand
  by_cases hx : |x| < 1
  · have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    rw [min_eq_right hx2]
    have e : Complex.exp ((x : ℂ) * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I * (if |x| < 1 then 1 else 0)
        = Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I := by
      simp only [hx, if_true, mul_one]; push_cast; ring_nf
    rw [e]
    refine (taylor_bound (x * ξ)).trans ?_
    nlinarith [sq_nonneg x, sq_nonneg ξ, mul_nonneg (sq_nonneg ξ) (sq_nonneg x)]
  · have hx2 : 1 ≤ x ^ 2 := by
      rw [not_lt] at hx; nlinarith [sq_abs x, abs_nonneg x]
    rw [min_eq_left hx2]
    have e : Complex.exp ((x : ℂ) * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I * (if |x| < 1 then 1 else 0)
        = Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 := by
      simp only [hx, if_false, mul_zero, sub_zero]; push_cast; ring_nf
    rw [e]
    calc ‖Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
      _ ≤ (3 * ξ ^ 2 + 2) * 1 := by nlinarith [sq_nonneg ξ]

open LevyFoundations in
theorem comp_integrable (η : Measure ℝ) (hη : isLevyMeasure η) (ξ : ℝ) :
    Integrable (fun x : ℝ => compensatedIntegrand ξ x) η := by
  have hmeas : Measurable (fun x : ℝ => min 1 (x ^ 2)) := measurable_const.min (by fun_prop)
  have hint : Integrable (fun x : ℝ => min 1 (x ^ 2)) η := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
    exact hη.2
  refine Integrable.mono' (hint.const_mul (3 * ξ ^ 2 + 2)) (comp_measurable ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => comp_bound ξ x)

open LevyFoundations in
theorem comp_re (ξ x : ℝ) : (compensatedIntegrand ξ x).re = Real.cos (ξ * x) - 1 := by
  unfold compensatedIntegrand
  have e : (x : ℂ) * ↑ξ * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  by_cases hx : |x| < 1
  · simp only [hx, if_true, mul_one, Complex.sub_re, Complex.one_re, e, Complex.exp_ofReal_mul_I_re]
    simp [mul_comm]
  · simp only [hx, if_false, mul_zero, sub_zero, Complex.sub_re, Complex.one_re, e, Complex.exp_ofReal_mul_I_re]
    simp [mul_comm]

open LevyFoundations in
theorem re_exponent (T : LevyKhintchineTriple) (ξ : ℝ) :
    (exponent T ξ).re = -(T.gaussianVariance : ℝ) * ξ ^ 2 / 2
      + ∫ x, (Real.cos (ξ * x) - 1) ∂T.levyMeasure := by
  unfold exponent
  have hint := comp_integrable T.levyMeasure T.levyMeasure_condition ξ
  have h1 : (∫ x, compensatedIntegrand ξ x ∂T.levyMeasure).re
      = ∫ x, (compensatedIntegrand ξ x).re ∂T.levyMeasure := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    exact this.symm
  have hsq : ((ξ : ℂ) ^ 2).re = ξ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [Complex.add_re, Complex.sub_re, h1, comp_re]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hsq]
  ring

open Complex in
theorem nz_normsq (ν : Measure ℝ) [IsProbabilityMeasure ν] (ξ : ℝ) :
    ‖charFun ν ξ‖ ^ 2 = ∫ z : ℝ × ℝ, Real.cos (ξ * (z.1 - z.2)) ∂(ν.prod ν) := by
  set f : ℝ → ℂ := fun x => cexp ((ξ : ℂ) * x * I) with hf
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hfn : ∀ x, ‖f x‖ = 1 := fun x => by
    simp only [hf]
    have : (ξ : ℂ) * x * I = ((ξ * x : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ g : ℝ → ℂ, Continuous g → (∀ x, ‖g x‖ = 1) → Integrable g ν := by
    intro g hg hgn
    refine Integrable.of_bound (C := 1) hg.aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hgn x).le)
  have hψ : charFun ν ξ = ∫ x, f x ∂ν := by simp [charFun_apply_real, hf]
  have hconj : (starRingEnd ℂ) (charFun ν ξ) = ∫ y, (starRingEnd ℂ) (f y) ∂ν := by
    rw [hψ]; exact (integral_conj).symm
  have hprod : charFun ν ξ * (starRingEnd ℂ) (charFun ν ξ)
      = ∫ z : ℝ × ℝ, f z.1 * (starRingEnd ℂ) (f z.2) ∂(ν.prod ν) := by
    rw [hconj, hψ]
    exact (integral_prod_mul (μ := ν) (ν := ν) f (fun y => (starRingEnd ℂ) (f y))).symm
  have hmul : charFun ν ξ * (starRingEnd ℂ) (charFun ν ξ) = ((‖charFun ν ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj]; simp [Complex.normSq_eq_norm_sq]
  have hI : Integrable (fun z : ℝ × ℝ => f z.1 * (starRingEnd ℂ) (f z.2)) (ν.prod ν) := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ => f z.1 * (starRingEnd ℂ) (f z.2)).aestronglyMeasurable
    · simp [hfn]
  have heq : ((‖charFun ν ξ‖ ^ 2 : ℝ) : ℂ) = ∫ z : ℝ × ℝ, f z.1 * (starRingEnd ℂ) (f z.2) ∂(ν.prod ν) :=
    hmul.symm.trans hprod
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  have h2 := integral_re hI
  simp only [RCLike.re_to_complex] at h2
  rw [hre, ← h2]
  congr 1; ext z
  simp only [hf]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : (ξ : ℂ) * (z.1 : ℂ) * I + (starRingEnd ℂ) ((ξ : ℂ) * (z.2 : ℂ) * I)
      = ((ξ * (z.1 - z.2) : ℝ) : ℂ) * I := by
    simp [Complex.conj_ofReal]; push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]



open LevyFoundations in
/-- `g T ξ = 1 - |exp (ψ_T ξ)|²`. -/
noncomputable def gfun (T : LevyKhintchineTriple) (ξ : ℝ) : ℝ := 1 - Real.exp (2 * (exponent T ξ).re)

open LevyFoundations in
theorem gfun_repr (T : LevyKhintchineTriple) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ ξ, charFun μ ξ = Complex.exp (exponent T ξ)) (ξ : ℝ) :
    gfun T ξ = ∫ z : ℝ × ℝ, (1 - Real.cos (ξ * (z.1 - z.2))) ∂(μ.prod μ) := by
  have h := nz_normsq μ ξ
  rw [hμ ξ, Complex.norm_exp] at h
  have hi : Integrable (fun z : ℝ × ℝ => Real.cos (ξ * (z.1 - z.2))) (μ.prod μ) := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ => Real.cos (ξ * (z.1 - z.2))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  rw [integral_sub (integrable_const _) hi, ← h]
  unfold gfun
  rw [← Real.exp_nat_mul]
  simp

theorem trig_quasi (s t : ℝ) :
    1 - Real.cos (s + t) ≤ 2 * (1 - Real.cos s) + 2 * (1 - Real.cos t) := by
  have h1 : ∀ θ : ℝ, 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    intro θ
    have h3 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h3
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have key : Real.sin ((s + t) / 2) ^ 2 ≤ 2 * Real.sin (s / 2) ^ 2 + 2 * Real.sin (t / 2) ^ 2 := by
    have e : (s + t) / 2 = s / 2 + t / 2 := by ring
    rw [e, Real.sin_add]
    have hc1 := Real.abs_cos_le_one (s / 2)
    have hc2 := Real.abs_cos_le_one (t / 2)
    have : |Real.sin (s / 2) * Real.cos (t / 2) + Real.cos (s / 2) * Real.sin (t / 2)|
        ≤ |Real.sin (s / 2)| + |Real.sin (t / 2)| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      nlinarith [abs_nonneg (Real.sin (s / 2)), abs_nonneg (Real.sin (t / 2)), abs_nonneg (Real.cos (s / 2)), abs_nonneg (Real.cos (t / 2))]
    have h3 := sq_le_sq' (by linarith [abs_nonneg (Real.sin (s / 2) * Real.cos (t / 2) + Real.cos (s / 2) * Real.sin (t / 2)), neg_abs_le (Real.sin (s / 2) * Real.cos (t / 2) + Real.cos (s / 2) * Real.sin (t / 2)), abs_nonneg (Real.sin (s / 2)), abs_nonneg (Real.sin (t / 2))]) (le_trans (le_abs_self _) this)
    nlinarith [sq_abs (Real.sin (s / 2)), sq_abs (Real.sin (t / 2)), sq_nonneg (|Real.sin (s / 2)| - |Real.sin (t / 2)|)]
  have e2 : 1 - Real.cos (s + t) = 2 * Real.sin ((s + t) / 2) ^ 2 := by
    have := h1 (s + t); exact this
  rw [e2, h1 s, h1 t]
  nlinarith [key]

open LevyFoundations in
theorem gfun_quasi (T : LevyKhintchineTriple) (a b : ℝ) :
    gfun T (a + b) ≤ 2 * gfun T a + 2 * gfun T b := by
  obtain ⟨μ, hμp, -, hμ⟩ := levy_foundations_converse T
  have hi : ∀ c : ℝ, Integrable (fun z : ℝ × ℝ => (1 - Real.cos (c * (z.1 - z.2)))) (μ.prod μ) := by
    intro c
    refine Integrable.of_bound (C := 2) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ => (1 - Real.cos (c * (z.1 - z.2)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [Real.cos_le_one (c * (z.1 - z.2)), Real.neg_one_le_cos (c * (z.1 - z.2))]
  rw [gfun_repr T μ hμ, gfun_repr T μ hμ, gfun_repr T μ hμ, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi a).const_mul 2) ((hi b).const_mul 2)]
  refine integral_mono (hi _) (((hi a).const_mul 2).add ((hi b).const_mul 2)) (fun z => ?_)
  simp only
  have := trig_quasi (a * (z.1 - z.2)) (b * (z.1 - z.2))
  have e : (a + b) * (z.1 - z.2) = a * (z.1 - z.2) + b * (z.1 - z.2) := by ring
  rw [e]; exact this

open LevyFoundations in
theorem gfun_even (T : LevyKhintchineTriple) (ξ : ℝ) : gfun T (-ξ) = gfun T ξ := by
  unfold gfun
  rw [re_exponent, re_exponent]
  simp [neg_mul, Real.cos_neg]

open LevyFoundations in
theorem levy_finite_tail (η : Measure ℝ) (hη : isLevyMeasure η) {r : ℝ} (hr : 0 < r) :
    η {x : ℝ | r ≤ |x|} < ⊤ := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (by fun_prop))
  set c := ENNReal.ofReal (min 1 (r ^ 2))
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (lt_min one_pos (sq_pos_of_pos hr))
  have hsub : {x : ℝ | r ≤ |x|} ⊆ {x : ℝ | c ≤ ENNReal.ofReal (min 1 (x ^ 2))} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min le_rfl ((sq_abs x).symm ▸ pow_le_pow_left₀ hr.le hx 2)
  have hM := mul_meas_ge_le_lintegral hmeas c (μ := η)
  have hle : c * η {x : ℝ | r ≤ |x|} ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂η :=
    le_trans (mul_le_mul_right (measure_mono hsub) c) hM
  exact ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hη.2.ne hle) hc.ne'

open LevyFoundations in
theorem levy_sigmaFinite (η : Measure ℝ) (hη : isLevyMeasure η) : SigmaFinite η := by
  refine ⟨⟨{ set := fun k : ℕ => {x : ℝ | 1 / ((k : ℝ) + 1) ≤ |x|} ∪ {0}
             set_mem := fun _ => trivial
             finite := fun k => ?_
             spanning := ?_ }⟩⟩
  · refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [hη.1, add_zero]
    exact levy_finite_tail η hη (by positivity)
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x = 0
    · exact ⟨0, Or.inr hx⟩
    · obtain ⟨k, hk⟩ := exists_nat_gt (1 / |x|)
      refine ⟨k, Or.inl ?_⟩
      have hx' : 0 < |x| := abs_pos.2 hx
      have : 1 / ((k : ℝ) + 1) ≤ |x| := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hx'] at hk
        nlinarith
      exact this

theorem one_sub_cos_bound (ξ x : ℝ) : |1 - Real.cos (ξ * x)| ≤ (ξ ^ 2 + 2) * min 1 (x ^ 2) := by
  have h0 : 0 ≤ 1 - Real.cos (ξ * x) := by linarith [Real.cos_le_one (ξ * x)]
  rw [abs_of_nonneg h0]
  by_cases hx : x ^ 2 ≤ 1
  · rw [min_eq_right hx]
    have := Real.one_sub_sq_div_two_le_cos (x := ξ * x)
    nlinarith [sq_nonneg x, sq_nonneg ξ, mul_nonneg (sq_nonneg ξ) (sq_nonneg x)]
  · rw [not_le] at hx
    rw [min_eq_left hx.le]
    nlinarith [Real.neg_one_le_cos (ξ * x), sq_nonneg ξ]

open LevyFoundations in
theorem avg_swap (η : Measure ℝ) (hη : isLevyMeasure η) (δ : ℝ) (hδ : 0 < δ) :
    ∫ ξ in (0 : ℝ)..δ, ∫ x, (1 - Real.cos (ξ * x)) ∂η
      = ∫ x, (∫ ξ in (0 : ℝ)..δ, (1 - Real.cos (ξ * x))) ∂η := by
  haveI := levy_sigmaFinite η hη
  have hmeas : Measurable (fun x : ℝ => min 1 (x ^ 2)) := measurable_const.min (by fun_prop)
  have hint : Integrable (fun x : ℝ => min 1 (x ^ 2)) η := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
    exact hη.2
  set μ : Measure ℝ := volume.restrict (Set.Ioc 0 δ) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; exact ⟨by simp⟩
  have hξint : Integrable (fun ξ : ℝ => ξ ^ 2 + 2) μ :=
    (by fun_prop : Continuous fun ξ : ℝ => ξ ^ 2 + 2).integrableOn_Ioc
  have hprod : Integrable (fun z : ℝ × ℝ => (z.1 ^ 2 + 2) * min 1 (z.2 ^ 2)) (μ.prod η) :=
    hξint.mul_prod hint
  have hF : Integrable (fun z : ℝ × ℝ => 1 - Real.cos (z.1 * z.2)) (μ.prod η) := by
    refine Integrable.mono' hprod ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ => 1 - Real.cos (z.1 * z.2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact one_sub_cos_bound z.1 z.2
  rw [intervalIntegral.integral_of_le hδ.le]
  have hswap := integral_integral_swap (μ := μ) (ν := η) (f := fun ξ x => 1 - Real.cos (ξ * x)) hF
  rw [hswap]
  congr 1
  ext x
  rw [intervalIntegral.integral_of_le hδ.le]

open Filter Topology

theorem uniform_small (g : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hcont : ∀ n, Continuous (g n)) (hG : Continuous G) (hG0 : G 0 = 0)
    (hbd : ∀ n ξ, 0 ≤ g n ξ ∧ g n ξ ≤ 1) (heven : ∀ n ξ, g n (-ξ) = g n ξ)
    (hq : ∀ n a b, g n (a + b) ≤ 2 * g n a + 2 * g n b)
    (hlim : ∀ ξ, Tendsto (fun n => g n ξ) atTop (𝓝 (G ξ))) :
    ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ ξ : ℝ, |ξ| ≤ δ → g n ξ ≤ ε := by
  intro ε hε
  obtain ⟨δ0, hδ0, hδG⟩ := Metric.continuous_iff.1 hG 0 (ε / 12) (by positivity)
  set δ : ℝ := δ0 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hGsmall : ∀ ξ, |ξ| ≤ δ → G ξ ≤ ε / 12 := by
    intro ξ hξ
    have := hδG ξ (by rw [Real.dist_eq, sub_zero]; linarith)
    rw [hG0, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  refine ⟨δ, hδ, ?_⟩
  -- integrals converge
  have hint : Tendsto (fun n => ∫ x in (0 : ℝ)..δ, g n x) atTop (𝓝 (∫ x in (0 : ℝ)..δ, G x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun n => (hcont n).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbd n x).1]; exact (hbd n x).2
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun x _ => hlim x
  have hGint : ∫ x in (0 : ℝ)..δ, G x ≤ δ * (ε / 12) := by
    calc ∫ x in (0 : ℝ)..δ, G x ≤ ∫ x in (0 : ℝ)..δ, ε / 12 := by
          refine intervalIntegral.integral_mono_on hδ.le (hG.intervalIntegrable _ _) intervalIntegrable_const ?_
          intro x hx
          exact hGsmall x (by rw [abs_of_nonneg hx.1]; exact hx.2)
      _ = δ * (ε / 12) := by simp; ring
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hint) (δ * (ε / 12)) (by positivity)
  refine ⟨N, fun n hn ξ hξ => ?_⟩
  have hnint : ∫ x in (0 : ℝ)..δ, g n x ≤ δ * (ε / 6) := by
    have := hN n hn
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    linarith
  -- key inequality for ξ ∈ [0, δ]
  have hkey : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ δ → δ * g n ξ ≤ 6 * ∫ x in (0 : ℝ)..δ, g n x := by
    intro ξ h0 hξδ
    have hI : ∀ a b : ℝ, IntervalIntegrable (g n) volume a b := fun a b => (hcont n).intervalIntegrable a b
    have hJc : Continuous (fun x : ℝ => g n (ξ - x)) := (hcont n).comp (continuous_const.sub continuous_id)
    have hJ : IntervalIntegrable (fun x : ℝ => g n (ξ - x)) volume 0 δ := hJc.intervalIntegrable _ _
    have h1 : ∫ x in (0 : ℝ)..δ, g n ξ = δ * g n ξ := by simp
    have h2 : ∫ x in (0 : ℝ)..δ, g n ξ ≤ ∫ x in (0 : ℝ)..δ, (2 * g n x + 2 * g n (ξ - x)) := by
      refine intervalIntegral.integral_mono_on hδ.le intervalIntegrable_const
        (((hI 0 δ).const_mul 2).add (hJ.const_mul 2)) ?_
      intro x hx
      have := hq n x (ξ - x)
      rw [show x + (ξ - x) = ξ by ring] at this
      exact this
    have h3 : ∫ x in (0 : ℝ)..δ, (2 * g n x + 2 * g n (ξ - x))
        = 2 * (∫ x in (0 : ℝ)..δ, g n x) + 2 * (∫ x in (0 : ℝ)..δ, g n (ξ - x)) := by
      rw [intervalIntegral.integral_add ((hI 0 δ).const_mul 2) (hJ.const_mul 2)]
      simp only [intervalIntegral.integral_const_mul]
    have h4 : ∫ x in (0 : ℝ)..δ, g n (ξ - x) = ∫ x in (ξ - δ)..ξ, g n x := by
      rw [intervalIntegral.integral_comp_sub_left (fun x => g n x) ξ]
      simp
    have h5 : ∫ x in (ξ - δ)..ξ, g n x ≤ ∫ x in (-δ)..δ, g n x := by
      refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall fun x => (hbd n x).1) (hI _ _)
    have h6 : ∫ x in (-δ)..δ, g n x = 2 * ∫ x in (0 : ℝ)..δ, g n x := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-δ) 0) (hI 0 δ)]
      have : ∫ x in (-δ)..0, g n x = ∫ x in (0 : ℝ)..δ, g n x := by
        have := intervalIntegral.integral_comp_neg (a := 0) (b := δ) (fun x => g n x)
        simp only [heven] at this
        rw [this]; simp
      rw [this]; ring
    linarith
  by_cases hξ0 : 0 ≤ ξ
  · have := hkey ξ hξ0 (by rw [abs_of_nonneg hξ0] at hξ; exact hξ)
    have hpos : 0 < δ := hδ
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  · have hneg : 0 ≤ -ξ := by linarith
    have := hkey (-ξ) hneg (by rw [abs_of_neg (not_le.1 hξ0)] at hξ; exact hξ)
    rw [heven] at this
    by_contra hcon
    rw [not_le] at hcon
    nlinarith

noncomputable def Kk (x : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..1, (1 - Real.cos (ξ * x))

theorem Kk_eq {y : ℝ} (hy : y ≠ 0) : Kk y = 1 - Real.sin y / y := by
  unfold Kk
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun ξ : ℝ => Real.cos (ξ * y)).intervalIntegrable _ _)]
  have := intervalIntegral.integral_comp_mul_right (a := 0) (b := 1) (fun t => Real.cos t) hy
  simp only [zero_mul, one_mul, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul] at this
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [this]; field_simp

theorem Kk_nonneg (x : ℝ) : 0 ≤ Kk x := by
  unfold Kk
  refine intervalIntegral.integral_nonneg zero_le_one (fun ξ _ => ?_)
  linarith [Real.cos_le_one (ξ * x)]

theorem Kk_le_two (x : ℝ) : Kk x ≤ 2 := by
  unfold Kk
  calc ∫ ξ in (0 : ℝ)..1, (1 - Real.cos (ξ * x)) ≤ ∫ ξ in (0 : ℝ)..1, (2 : ℝ) := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((by fun_prop : Continuous fun ξ : ℝ => 1 - Real.cos (ξ * x)).intervalIntegrable _ _)
          intervalIntegrable_const (fun ξ _ => ?_)
        linarith [Real.neg_one_le_cos (ξ * x)]
    _ = 2 := by simp

theorem Kk_le_sq (x : ℝ) : Kk x ≤ x ^ 2 / 6 := by
  unfold Kk
  calc ∫ ξ in (0 : ℝ)..1, (1 - Real.cos (ξ * x)) ≤ ∫ ξ in (0 : ℝ)..1, (ξ ^ 2 * x ^ 2 / 2) := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((by fun_prop : Continuous fun ξ : ℝ => 1 - Real.cos (ξ * x)).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun ξ : ℝ => ξ ^ 2 * x ^ 2 / 2).intervalIntegrable _ _) (fun ξ _ => ?_)
        have := Real.one_sub_sq_div_two_le_cos (x := ξ * x)
        nlinarith
    _ = x ^ 2 / 6 := by
        simp [integral_pow]; ring

theorem Kk_ge_half {y : ℝ} (hy : 2 ≤ |y|) : 1 / 2 ≤ Kk y := by
  have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy; linarith
  rw [Kk_eq hy0]
  have h1 : |Real.sin y / y| ≤ 1 / 2 := by
    rw [abs_div, div_le_iff₀ (by linarith)]
    have := Real.abs_sin_le_one y
    linarith
  have := (abs_le.1 h1).2
  linarith

theorem one_sub_cos_ge (u : ℝ) (hu : |u| ≤ Real.pi) : 2 * u ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos u := by
  have hpi := Real.pi_pos
  have h1 : 1 - Real.cos u = 2 * Real.sin (|u| / 2) ^ 2 := by
    have h3 := Real.cos_two_mul (|u| / 2)
    rw [show 2 * (|u| / 2) = |u| by ring, Real.cos_abs] at h3
    nlinarith [Real.sin_sq_add_cos_sq (|u| / 2)]
  rw [h1]
  have h2 : 2 / Real.pi * (|u| / 2) ≤ Real.sin (|u| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  have h4 : (|u| / Real.pi) ≤ Real.sin (|u| / 2) := by
    have : 2 / Real.pi * (|u| / 2) = |u| / Real.pi := by field_simp
    linarith
  have h5 : 0 ≤ |u| / Real.pi := by positivity
  have h6 := pow_le_pow_left₀ h5 h4 2
  have : (|u| / Real.pi) ^ 2 = u ^ 2 / Real.pi ^ 2 := by rw [div_pow, sq_abs]
  rw [this] at h6
  have e : 2 * u ^ 2 / Real.pi ^ 2 = 2 * (u ^ 2 / Real.pi ^ 2) := by ring
  rw [e]
  linarith

theorem Kk_lower (x : ℝ) : (1 / 20) * min 1 (x ^ 2) ≤ Kk x := by
  by_cases hx : 2 ≤ |x|
  · have := Kk_ge_half hx
    have hm : min 1 (x ^ 2) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [not_le] at hx
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have h1 : ∫ ξ in (0 : ℝ)..1, (2 * (ξ * x) ^ 2 / Real.pi ^ 2) ≤ Kk x := by
      unfold Kk
      refine intervalIntegral.integral_mono_on zero_le_one
        ((by fun_prop : Continuous fun ξ : ℝ => 2 * (ξ * x) ^ 2 / Real.pi ^ 2).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun ξ : ℝ => 1 - Real.cos (ξ * x)).intervalIntegrable _ _) (fun ξ hξ => ?_)
      apply one_sub_cos_ge
      rw [abs_mul, abs_of_nonneg hξ.1]
      nlinarith [hξ.2, abs_nonneg x, Real.pi_gt_three]
    have h2 : ∫ ξ in (0 : ℝ)..1, (2 * (ξ * x) ^ 2 / Real.pi ^ 2) = 2 * x ^ 2 / (3 * Real.pi ^ 2) := by
      have : ∀ ξ : ℝ, 2 * (ξ * x) ^ 2 / Real.pi ^ 2 = (2 * x ^ 2 / Real.pi ^ 2) * ξ ^ 2 := fun ξ => by ring
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul]
      simp [integral_pow]; field_simp; ring
    rw [h2] at h1
    have hm : min 1 (x ^ 2) ≤ x ^ 2 := min_le_right _ _
    have hpi2 : Real.pi ^ 2 < 9.93 := by nlinarith
    have : (1 / 20) * x ^ 2 ≤ 2 * x ^ 2 / (3 * Real.pi ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg x]
    nlinarith


open LevyFoundations in
theorem exponent_zero (T : LevyKhintchineTriple) : exponent T 0 = 0 := by
  unfold exponent
  have : ∀ x : ℝ, compensatedIntegrand 0 x = 0 := fun x => by simp [compensatedIntegrand]
  simp [this]

open LevyFoundations in
/-- `fT T ξ = - Re ψ_T(ξ)`. -/
noncomputable def fT (T : LevyKhintchineTriple) (ξ : ℝ) : ℝ := -(exponent T ξ).re

open LevyFoundations in
theorem fT_formula (T : LevyKhintchineTriple) (ξ : ℝ) :
    fT T ξ = (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 + ∫ x, (1 - Real.cos (ξ * x)) ∂T.levyMeasure := by
  unfold fT
  rw [re_exponent]
  have : ∫ x, (Real.cos (ξ * x) - 1) ∂T.levyMeasure = -∫ x, (1 - Real.cos (ξ * x)) ∂T.levyMeasure := by
    rw [← integral_neg]; congr 1; ext x; ring
  rw [this]; ring

open LevyFoundations in
theorem fT_integrable (T : LevyKhintchineTriple) (ξ : ℝ) :
    Integrable (fun x : ℝ => 1 - Real.cos (ξ * x)) T.levyMeasure := by
  have hmeas : Measurable (fun x : ℝ => min 1 (x ^ 2)) := measurable_const.min (by fun_prop)
  have hint : Integrable (fun x : ℝ => min 1 (x ^ 2)) T.levyMeasure := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
    exact T.levyMeasure_condition.2
  refine Integrable.mono' (hint.const_mul (ξ ^ 2 + 2))
    (by fun_prop : Continuous fun x : ℝ => 1 - Real.cos (ξ * x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]; exact one_sub_cos_bound ξ x

open LevyFoundations in
theorem fT_nonneg (T : LevyKhintchineTriple) (ξ : ℝ) : 0 ≤ fT T ξ := by
  rw [fT_formula]
  have : 0 ≤ ∫ x, (1 - Real.cos (ξ * x)) ∂T.levyMeasure :=
    integral_nonneg fun x => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ξ * x)]
  have h2 : 0 ≤ (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 := by positivity
  linarith

open LevyFoundations in
theorem fT_quasi (T : LevyKhintchineTriple) (a b : ℝ) :
    fT T (a + b) ≤ 2 * fT T a + 2 * fT T b := by
  rw [fT_formula, fT_formula, fT_formula]
  have hi := fT_integrable T
  have h1 : ∫ x, (1 - Real.cos ((a + b) * x)) ∂T.levyMeasure
      ≤ 2 * ∫ x, (1 - Real.cos (a * x)) ∂T.levyMeasure + 2 * ∫ x, (1 - Real.cos (b * x)) ∂T.levyMeasure := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi a).const_mul 2) ((hi b).const_mul 2)]
    refine integral_mono (hi _) (((hi a).const_mul 2).add ((hi b).const_mul 2)) (fun x => ?_)
    simp only
    have := trig_quasi (a * x) (b * x)
    rw [show (a + b) * x = a * x + b * x by ring]
    exact this
  have h2 : (T.gaussianVariance : ℝ) * (a + b) ^ 2 / 2
      ≤ 2 * ((T.gaussianVariance : ℝ) * a ^ 2 / 2) + 2 * ((T.gaussianVariance : ℝ) * b ^ 2 / 2) := by
    have := NNReal.coe_nonneg T.gaussianVariance
    nlinarith [mul_nonneg this (sq_nonneg (a - b))]
  linarith

open LevyFoundations in
theorem fT_double (T : LevyKhintchineTriple) (ξ : ℝ) : fT T (2 * ξ) ≤ 4 * fT T ξ := by
  have := fT_quasi T ξ ξ
  rw [← two_mul] at this
  linarith

open LevyFoundations in
theorem gfun_eq (T : LevyKhintchineTriple) (ξ : ℝ) : gfun T ξ = 1 - Real.exp (-2 * fT T ξ) := by
  unfold gfun fT; congr 2; ring

open LevyFoundations in
theorem fT_le_gfun (T : LevyKhintchineTriple) (ξ : ℝ) (h : gfun T ξ ≤ 1 / 2) : fT T ξ ≤ gfun T ξ := by
  have hg := gfun_eq T ξ
  set f := fT T ξ with hf
  have hf0 : 0 ≤ f := fT_nonneg T ξ
  have he : Real.exp (-2 * f) = 1 - gfun T ξ := by rw [hg]; ring
  have hpos : 0 < Real.exp (-2 * f) := Real.exp_pos _
  have h1 : Real.exp (2 * f) * Real.exp (-2 * f) = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (2 * f) ≤ 1 + 2 * gfun T ξ := by
    have hg0 : 0 ≤ gfun T ξ := by rw [hg]; have := Real.exp_le_one_iff.2 (by linarith : -2 * f ≤ 0); linarith
    rw [he] at h1
    nlinarith [Real.exp_pos (2 * f)]
  have h3 := Real.add_one_le_exp (2 * f)
  linarith

open LevyFoundations in
theorem seq_small (T : ℕ → LevyKhintchineTriple) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hlim : ∀ ξ : ℝ, Tendsto (fun n => exponent (T n) ξ) atTop (𝓝 (ψ ξ))) :
    ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ ξ : ℝ, |ξ| ≤ δ → fT (T n) ξ ≤ ε := by
  intro ε hε
  have hre : ∀ ξ, Tendsto (fun n => (exponent (T n) ξ).re) atTop (𝓝 (ψ ξ).re) :=
    fun ξ => (Complex.continuous_re.tendsto _).comp (hlim ξ)
  have hlim' : ∀ ξ, Tendsto (fun n => gfun (T n) ξ) atTop (𝓝 (1 - Real.exp (2 * (ψ ξ).re))) := by
    intro ξ
    unfold gfun
    exact tendsto_const_nhds.sub ((Real.continuous_exp.tendsto _).comp (((hre ξ).const_mul 2)))
  have hG : Continuous (fun ξ => 1 - Real.exp (2 * (ψ ξ).re)) := by
    have := Complex.continuous_re.comp hψ
    fun_prop
  have hψ0 : ψ 0 = 0 := by
    have := hlim 0
    simp only [exponent_zero] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have hG0 : (fun ξ => 1 - Real.exp (2 * (ψ ξ).re)) 0 = 0 := by simp [hψ0]
  have hcont : ∀ n, Continuous (gfun (T n)) := by
    intro n
    unfold gfun
    have := Complex.continuous_re.comp (levy_foundations_exponentContinuous (T n))
    fun_prop
  have hbd : ∀ n ξ, 0 ≤ gfun (T n) ξ ∧ gfun (T n) ξ ≤ 1 := by
    intro n ξ
    rw [gfun_eq]
    have h1 : Real.exp (-2 * fT (T n) ξ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [fT_nonneg (T n) ξ])
    exact ⟨by linarith, by linarith [Real.exp_pos (-2 * fT (T n) ξ)]⟩
  obtain ⟨δ, hδ, N, hN⟩ := uniform_small (fun n => gfun (T n)) (fun ξ => 1 - Real.exp (2 * (ψ ξ).re))
    hcont hG hG0 hbd (fun n ξ => gfun_even (T n) ξ) (fun n a b => gfun_quasi (T n) a b) hlim'
    (min ε (1 / 2)) (lt_min hε (by norm_num))
  refine ⟨δ, hδ, N, fun n hn ξ hξ => ?_⟩
  have hg := hN n hn ξ hξ
  have hg2 : gfun (T n) ξ ≤ 1 / 2 := hg.trans (min_le_right _ _)
  exact (fT_le_gfun (T n) ξ hg2).trans (hg.trans (min_le_left _ _))

open LevyFoundations in
theorem seq_bound (T : ℕ → LevyKhintchineTriple) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hlim : ∀ ξ : ℝ, Tendsto (fun n => exponent (T n) ξ) atTop (𝓝 (ψ ξ))) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → fT (T n) ξ ≤ C := by
  obtain ⟨δ, hδ, N, hN⟩ := seq_small T ψ hψ hlim 1 one_pos
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
  refine ⟨4 ^ j, N, fun n hn ξ h0 h1 => ?_⟩
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hξ' : |ξ / 2 ^ j| ≤ δ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ h2j]
    have := (div_lt_iff₀ hδ).1 hj
    nlinarith
  have hbase := hN n hn (ξ / 2 ^ j) hξ'
  have hiter : ∀ k : ℕ, fT (T n) (2 ^ k * (ξ / 2 ^ j)) ≤ 4 ^ k * fT (T n) (ξ / 2 ^ j) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := fT_double (T n) (2 ^ k * (ξ / 2 ^ j))
      rw [show 2 * (2 ^ k * (ξ / 2 ^ j)) = 2 ^ (k + 1) * (ξ / 2 ^ j) by ring] at this
      calc fT (T n) (2 ^ (k + 1) * (ξ / 2 ^ j)) ≤ 4 * fT (T n) (2 ^ k * (ξ / 2 ^ j)) := this
        _ ≤ 4 * (4 ^ k * fT (T n) (ξ / 2 ^ j)) := by linarith
        _ = 4 ^ (k + 1) * fT (T n) (ξ / 2 ^ j) := by ring
  have := hiter j
  rw [show (2 : ℝ) ^ j * (ξ / 2 ^ j) = ξ by field_simp] at this
  calc fT (T n) ξ ≤ 4 ^ j * fT (T n) (ξ / 2 ^ j) := this
    _ ≤ 4 ^ j * 1 := by gcongr
    _ = 4 ^ j := mul_one _

theorem Kk_scale (δ x : ℝ) : ∫ ξ in (0 : ℝ)..δ, (1 - Real.cos (ξ * x)) = δ * Kk (δ * x) := by
  by_cases hδ : δ = 0
  · subst hδ; simp
  have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun t => 1 - Real.cos (t * x)) hδ
  simp only [mul_zero, mul_one, smul_eq_mul] at this
  have e : Kk (δ * x) = ∫ ξ in (0 : ℝ)..1, (1 - Real.cos (δ * ξ * x)) := by
    unfold Kk
    congr 1; ext ξ; ring_nf
  rw [e, this, ← mul_assoc, mul_inv_cancel₀ hδ, one_mul]

open LevyFoundations in
theorem Kk_integrable (η : Measure ℝ) (hη : isLevyMeasure η) (δ : ℝ) :
    Integrable (fun x : ℝ => Kk (δ * x)) η := by
  have hmeas : Measurable (fun x : ℝ => min 1 (x ^ 2)) := measurable_const.min (by fun_prop)
  have hint : Integrable (fun x : ℝ => min 1 (x ^ 2)) η := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
    exact hη.2
  have hKc : Continuous Kk := by
    unfold Kk
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 1
  refine Integrable.mono' (hint.const_mul (2 * (δ ^ 2 + 1))) (hKc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Kk_nonneg _)]
  by_cases hx : x ^ 2 ≤ 1
  · rw [min_eq_right hx]
    have := Kk_le_sq (δ * x)
    nlinarith [sq_nonneg x, sq_nonneg δ, mul_nonneg (sq_nonneg δ) (sq_nonneg x)]
  · rw [not_le] at hx; rw [min_eq_left hx.le]
    have := Kk_le_two (δ * x)
    nlinarith [sq_nonneg δ]

open LevyFoundations in
theorem avg_f (T : LevyKhintchineTriple) (δ : ℝ) (hδ : 0 < δ) :
    ∫ ξ in (0 : ℝ)..δ, fT T ξ
      = (T.gaussianVariance : ℝ) * δ ^ 3 / 6 + δ * ∫ x, Kk (δ * x) ∂T.levyMeasure := by
  have hfc : ∀ ξ, fT T ξ = (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 + ∫ x, (1 - Real.cos (ξ * x)) ∂T.levyMeasure :=
    fT_formula T
  simp_rw [hfc]
  have hc : Continuous fun ξ : ℝ => ∫ x, (1 - Real.cos (ξ * x)) ∂T.levyMeasure := by
    have : (fun ξ : ℝ => ∫ x, (1 - Real.cos (ξ * x)) ∂T.levyMeasure) = fun ξ => fT T ξ - (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 := by
      ext ξ; rw [hfc]; ring
    rw [this]
    have h1 : Continuous (fT T) := by
      unfold fT
      exact (Complex.continuous_re.comp (levy_foundations_exponentContinuous T)).neg
    exact h1.sub (by fun_prop)
  have hg : Continuous fun ξ : ℝ => (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 := by fun_prop
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ ξ in (0 : ℝ)..δ, (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 = (T.gaussianVariance : ℝ) * δ ^ 3 / 6 := by
    have : ∀ ξ : ℝ, (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 = ((T.gaussianVariance : ℝ) / 2) * ξ ^ 2 := fun ξ => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul]
    simp [integral_pow]; ring
  rw [h1, avg_swap T.levyMeasure T.levyMeasure_condition δ hδ]
  congr 1
  simp_rw [Kk_scale]
  rw [integral_const_mul]

open LevyFoundations in
theorem mass_bound (T : ℕ → LevyKhintchineTriple) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hlim : ∀ ξ : ℝ, Tendsto (fun n => exponent (T n) ξ) atTop (𝓝 (ψ ξ))) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      ((T n).gaussianVariance : ℝ) / 6 + ∫ x, Kk x ∂(T n).levyMeasure ≤ C := by
  obtain ⟨C, N, hN⟩ := seq_bound T ψ hψ hlim
  refine ⟨C, N, fun n hn => ?_⟩
  have h := avg_f (T n) 1 one_pos
  simp only [one_pow, mul_one, one_mul] at h
  have hle : ∫ ξ in (0 : ℝ)..1, fT (T n) ξ ≤ ∫ ξ in (0 : ℝ)..1, C := by
    have hc : Continuous (fT (T n)) := by
      unfold fT
      exact (Complex.continuous_re.comp (levy_foundations_exponentContinuous (T n))).neg
    exact intervalIntegral.integral_mono_on zero_le_one (hc.intervalIntegrable _ _) intervalIntegrable_const
      (fun ξ hξ => hN n hn ξ hξ.1 hξ.2)
  rw [h] at hle
  simpa using hle

open LevyFoundations in
theorem tail_bound (T : ℕ → LevyKhintchineTriple) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hlim : ∀ ξ : ℝ, Tendsto (fun n => exponent (T n) ξ) atTop (𝓝 (ψ ξ))) :
    ∀ ε > 0, ∃ R > 0, ∃ N : ℕ, ∀ n ≥ N,
      ((T n).levyMeasure {x : ℝ | R ≤ |x|}).toReal ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := seq_small T ψ hψ hlim (ε / 2) (by positivity)
  refine ⟨2 / δ, by positivity, N, fun n hn => ?_⟩
  set η := (T n).levyMeasure with hη
  have hI := avg_f (T n) δ hδ
  have hc : Continuous (fT (T n)) := by
    unfold fT
    exact (Complex.continuous_re.comp (levy_foundations_exponentContinuous (T n))).neg
  have h1 : ∫ ξ in (0 : ℝ)..δ, fT (T n) ξ ≤ δ * (ε / 2) := by
    calc ∫ ξ in (0 : ℝ)..δ, fT (T n) ξ ≤ ∫ ξ in (0 : ℝ)..δ, ε / 2 :=
          intervalIntegral.integral_mono_on hδ.le (hc.intervalIntegrable _ _) intervalIntegrable_const
            (fun ξ hξ => hN n hn ξ (by rw [abs_of_nonneg hξ.1]; exact hξ.2))
      _ = δ * (ε / 2) := by simp; ring
  have h2 : 0 ≤ ((T n).gaussianVariance : ℝ) * δ ^ 3 / 6 := by positivity
  have h3 : ∫ x, Kk (δ * x) ∂η ≤ ε / 2 := by
    have : δ * ∫ x, Kk (δ * x) ∂η ≤ δ * (ε / 2) := by linarith
    exact le_of_mul_le_mul_left this hδ
  have hKi := Kk_integrable η (T n).levyMeasure_condition δ
  have hset : MeasurableSet {x : ℝ | 2 / δ ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
  have h4 : (1 / 2 : ℝ) * (η {x : ℝ | 2 / δ ≤ |x|}).toReal ≤ ∫ x, Kk (δ * x) ∂η := by
    have hfin : η {x : ℝ | 2 / δ ≤ |x|} < ⊤ := levy_finite_tail η (T n).levyMeasure_condition (by positivity)
    have : ∫ x in {x : ℝ | 2 / δ ≤ |x|}, (1 / 2 : ℝ) ∂η ≤ ∫ x in {x : ℝ | 2 / δ ≤ |x|}, Kk (δ * x) ∂η := by
      have hc1 : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) {x : ℝ | 2 / δ ≤ |x|} η :=
        integrableOn_const (hs := hfin.ne)
      refine setIntegral_mono_on hc1 hKi.integrableOn hset (fun x hx => ?_)
      refine Kk_ge_half ?_
      rw [abs_mul, abs_of_pos hδ]
      have : 2 / δ ≤ |x| := hx
      rw [div_le_iff₀ hδ] at this
      linarith
    have h5 : ∫ x in {x : ℝ | 2 / δ ≤ |x|}, (1 / 2 : ℝ) ∂η = (1 / 2 : ℝ) * (η {x : ℝ | 2 / δ ≤ |x|}).toReal := by
      rw [setIntegral_const]; simp [Measure.real]; ring
    have h6 : ∫ x in {x : ℝ | 2 / δ ≤ |x|}, Kk (δ * x) ∂η ≤ ∫ x, Kk (δ * x) ∂η :=
      setIntegral_le_integral hKi (Filter.Eventually.of_forall fun x => Kk_nonneg _)
    linarith
  linarith

theorem Kk_zero : Kk 0 = 0 := by simp [Kk]

theorem Kk_taylor (x : ℝ) (hx : |x| ≤ 1) : |Kk x - x ^ 2 / 6| ≤ x ^ 4 / 96 := by
  have h1 : Kk x - x ^ 2 / 6 = ∫ ξ in (0 : ℝ)..1, ((1 - Real.cos (ξ * x)) - (ξ * x) ^ 2 / 2) := by
    unfold Kk
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun ξ : ℝ => 1 - Real.cos (ξ * x)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun ξ : ℝ => (ξ * x) ^ 2 / 2).intervalIntegrable _ _)]
    congr 1
    have : ∫ ξ in (0 : ℝ)..1, (ξ * x) ^ 2 / 2 = x ^ 2 / 6 := by
      have e : ∀ ξ : ℝ, (ξ * x) ^ 2 / 2 = (x ^ 2 / 2) * ξ ^ 2 := fun ξ => by ring
      simp_rw [e]
      rw [intervalIntegral.integral_const_mul]
      simp [integral_pow]; ring
    rw [this]
  rw [h1]
  have h2 : |∫ ξ in (0 : ℝ)..1, ((1 - Real.cos (ξ * x)) - (ξ * x) ^ 2 / 2)|
      ≤ ∫ ξ in (0 : ℝ)..1, (5 / 96) * x ^ 4 * ξ ^ 4 := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine intervalIntegral.integral_mono_on zero_le_one
      ((by fun_prop : Continuous fun ξ : ℝ => |(1 - Real.cos (ξ * x)) - (ξ * x) ^ 2 / 2|).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun ξ : ℝ => (5 / 96) * x ^ 4 * ξ ^ 4).intervalIntegrable _ _) (fun ξ hξ => ?_)
    have hu : |ξ * x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hξ.1]; nlinarith [hξ.2, abs_nonneg x]
    have := Real.cos_bound hu
    have e : (1 - Real.cos (ξ * x)) - (ξ * x) ^ 2 / 2 = -(Real.cos (ξ * x) - (1 - (ξ * x) ^ 2 / 2)) := by ring
    rw [e, abs_neg]
    refine this.trans ?_
    have : |ξ * x| ^ 4 = ξ ^ 4 * x ^ 4 := by
      rw [abs_mul, abs_of_nonneg hξ.1, mul_pow]
      congr 1
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rw [this]; nlinarith [pow_nonneg hξ.1 4, sq_nonneg x, pow_nonneg (sq_nonneg x) 2]
  refine h2.trans ?_
  have : ∫ ξ in (0 : ℝ)..1, (5 / 96) * x ^ 4 * ξ ^ 4 = x ^ 4 / 96 := by
    rw [intervalIntegral.integral_const_mul]
    simp [integral_pow]; ring
  rw [this]

noncomputable def chi (x : ℝ) : ℝ := min 1 (max 0 (2 - 2 * |x|))

theorem chi_cont : Continuous chi := by unfold chi; fun_prop
theorem chi_nonneg (x : ℝ) : 0 ≤ chi x := le_min zero_le_one (le_max_left _ _)
theorem chi_le_one (x : ℝ) : chi x ≤ 1 := min_le_left _ _
theorem chi_of_le_half {x : ℝ} (h : |x| ≤ 1 / 2) : chi x = 1 := by
  unfold chi
  rw [min_eq_left]
  have : (1 : ℝ) ≤ 2 - 2 * |x| := by linarith
  exact this.trans (le_max_right _ _)
theorem chi_of_ge_one {x : ℝ} (h : 1 ≤ |x|) : chi x = 0 := by
  unfold chi
  have : max 0 (2 - 2 * |x|) = 0 := max_eq_left (by linarith)
  rw [this]; simp

noncomputable def cchi (ξ x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * ξ * Complex.I) - 1 - (x : ℂ) * ξ * Complex.I * (chi x : ℂ)

theorem cchi_zero (ξ : ℝ) : cchi ξ 0 = 0 := by simp [cchi]

theorem cchi_cont (ξ : ℝ) : Continuous (cchi ξ) := by
  unfold cchi
  have := Complex.continuous_ofReal.comp chi_cont
  fun_prop

noncomputable def Gfun (ξ x : ℝ) : ℂ :=
  if x = 0 then ((-3 * ξ ^ 2 : ℝ) : ℂ) else cchi ξ x / (Kk x : ℂ)

theorem Kk_pos {x : ℝ} (hx : x ≠ 0) : 0 < Kk x := by
  have h1 := Kk_lower x
  have h2 : 0 < min 1 (x ^ 2) := lt_min one_pos (by positivity)
  linarith

theorem Gfun_mul (ξ x : ℝ) : Gfun ξ x * (Kk x : ℂ) = cchi ξ x := by
  by_cases hx : x = 0
  · subst hx; simp [Gfun, Kk_zero, cchi_zero]
  · have : (Kk x : ℂ) ≠ 0 := by exact_mod_cast (Kk_pos hx).ne'
    simp [Gfun, hx, div_mul_cancel₀ _ this]

theorem cchi_norm_le (ξ x : ℝ) (hx : |x| ≤ 1 / 2) : ‖cchi ξ x‖ ≤ 3 * ξ ^ 2 * x ^ 2 := by
  unfold cchi
  rw [chi_of_le_half hx]
  have e : Complex.exp ((x : ℂ) * ξ * Complex.I) - 1 - (x : ℂ) * ξ * Complex.I * ((1 : ℝ) : ℂ)
      = Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring_nf
  rw [e]
  have hn : ‖Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hI : ‖((x * ξ : ℝ) : ℂ) * Complex.I‖ = |x * ξ| := by simp
  by_cases h : |x * ξ| ≤ 1
  · have := Complex.norm_exp_sub_one_sub_id_le (x := ((x * ξ : ℝ) : ℂ) * Complex.I) (by rw [hI]; exact h)
    rw [hI, sq_abs] at this
    nlinarith [sq_nonneg (x * ξ)]
  · rw [not_le] at h
    calc _ ≤ ‖Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ + ‖((x * ξ : ℝ) : ℂ) * Complex.I‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 2 + |x * ξ| := by rw [hn, hI]; norm_num
      _ ≤ 3 * ξ ^ 2 * x ^ 2 := by nlinarith [sq_abs (x * ξ), abs_nonneg (x * ξ)]

theorem cchi_norm_le_far (ξ x : ℝ) (hx : 1 / 2 ≤ |x|) : ‖cchi ξ x‖ ≤ 2 + |ξ| := by
  unfold cchi
  have hn : ‖Complex.exp ((x : ℂ) * ξ * Complex.I)‖ = 1 := by
    have : (x : ℂ) * ξ * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  have hxc : |x| * chi x ≤ 1 := by
    by_cases h1 : 1 ≤ |x|
    · rw [chi_of_ge_one h1]; simp
    · rw [not_le] at h1
      nlinarith [chi_nonneg x, chi_le_one x, abs_nonneg x]
  have h3 : ‖(x : ℂ) * ξ * Complex.I * (chi x : ℂ)‖ ≤ |ξ| := by
    have e : ‖(x : ℂ) * ξ * Complex.I * (chi x : ℂ)‖ = |x| * |ξ| * chi x := by
      simp [abs_of_nonneg (chi_nonneg x)]
    rw [e]
    nlinarith [abs_nonneg ξ, abs_nonneg x, chi_nonneg x]
  calc _ ≤ ‖Complex.exp ((x : ℂ) * ξ * Complex.I)‖ + ‖(1 : ℂ)‖ + ‖(x : ℂ) * ξ * Complex.I * (chi x : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 2 + |ξ| := by rw [hn, norm_one]; linarith [h3]

theorem Gfun_bound (ξ x : ℝ) : ‖Gfun ξ x‖ ≤ 80 * (2 + |ξ|) + 60 * ξ ^ 2 + 3 * ξ ^ 2 := by
  by_cases hx : x = 0
  · subst hx; simp [Gfun]; nlinarith [abs_nonneg ξ, sq_nonneg ξ]
  have hK := Kk_pos hx
  have hGx : Gfun ξ x = cchi ξ x / (Kk x : ℂ) := by simp [Gfun, hx]
  rw [hGx, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
  by_cases h : |x| ≤ 1 / 2
  · have h1 := cchi_norm_le ξ x h
    have h2 := Kk_lower x
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    rw [min_eq_right hx2] at h2
    have hx2p : 0 < x ^ 2 := by positivity
    rw [div_le_iff₀ hK]
    nlinarith [sq_nonneg ξ, abs_nonneg ξ, mul_nonneg (sq_nonneg ξ) hx2p.le]
  · rw [not_le] at h
    have h1 := cchi_norm_le_far ξ x h.le
    have h2 := Kk_lower x
    have hmin : 1 / 4 ≤ min 1 (x ^ 2) := by
      refine le_min (by norm_num) ?_
      nlinarith [sq_abs x, abs_nonneg x]
    rw [div_le_iff₀ hK]
    nlinarith [sq_nonneg ξ, abs_nonneg ξ]

theorem exp_taylor3 (u : ℝ) (hu : |u| ≤ 1) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I + (u : ℂ) ^ 2 / 2‖ ≤ |u| ^ 3 := by
  have hn : ‖(u : ℂ) * Complex.I‖ ≤ 1 := by simpa using hu
  have := Complex.exp_bound (x := (u : ℂ) * Complex.I) hn (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.factorial_one, Nat.factorial_two, Nat.cast_ofNat] at this
  have e : Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I + (u : ℂ) ^ 2 / 2
      = Complex.exp ((u : ℂ) * Complex.I) - (1 + (u : ℂ) * Complex.I + ((u : ℂ) * Complex.I) ^ 2 / 2) := by
    have : ((u : ℂ) * Complex.I) ^ 2 = -(u : ℂ) ^ 2 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [this]; ring
  rw [e]
  refine this.trans ?_
  have hI : ‖(u : ℂ) * Complex.I‖ = |u| := by simp
  rw [hI]
  have h0 : 0 ≤ |u| ^ 3 := by positivity
  norm_num [Nat.succ_eq_add_one, Nat.factorial]
  nlinarith [h0]

theorem Kk_cont : Continuous Kk := by
  unfold Kk
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 1

theorem Gfun_near (ξ x : ℝ) (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 2) (hξx : |x * ξ| ≤ 1) :
    ‖Gfun ξ x - Gfun ξ 0‖ ≤ 20 * |x| * (|ξ| ^ 3 + ξ ^ 2) := by
  have hK := Kk_pos hx0
  have hGx : Gfun ξ x = cchi ξ x / (Kk x : ℂ) := by simp [Gfun, hx0]
  have hG0 : Gfun ξ 0 = ((-3 * ξ ^ 2 : ℝ) : ℂ) := by simp [Gfun]
  have hx1 : |x| ≤ 1 := by linarith
  have hxsq : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hKl : x ^ 2 / 20 ≤ Kk x := by
    have := Kk_lower x; rw [min_eq_right hxsq] at this; linarith
  have hKc : (Kk x : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hchi : chi x = 1 := chi_of_le_half hx
  have hc : cchi ξ x = Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I := by
    unfold cchi; rw [hchi]; push_cast; ring_nf
  -- numerator
  have hnum : Gfun ξ x - Gfun ξ 0 = ((cchi ξ x + (((x * ξ) ^ 2 / 2 : ℝ) : ℂ)) + 3 * (ξ : ℂ) ^ 2 * (((Kk x - x ^ 2 / 6 : ℝ)) : ℂ)) / (Kk x : ℂ) := by
    rw [hGx, hG0]
    field_simp
    push_cast
    ring
  rw [hnum, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK, div_le_iff₀ hK]
  have h1 : ‖cchi ξ x + (((x * ξ) ^ 2 / 2 : ℝ) : ℂ)‖ ≤ |x * ξ| ^ 3 := by
    have := exp_taylor3 (x * ξ) hξx
    rw [hc]
    have e : Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I + (((x * ξ) ^ 2 / 2 : ℝ) : ℂ)
        = Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I + ((x * ξ : ℝ) : ℂ) ^ 2 / 2 := by
      push_cast; ring
    rw [e]; exact this
  have h2 : ‖3 * (ξ : ℂ) ^ 2 * (((Kk x - x ^ 2 / 6 : ℝ)) : ℂ)‖ ≤ 3 * ξ ^ 2 * (x ^ 4 / 96) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖3 * (ξ : ℂ) ^ 2‖ = 3 * ξ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; norm_num
    rw [this]
    gcongr
    exact Kk_taylor x hx1
  have h3 := (norm_add_le _ _).trans (add_le_add h1 h2)
  have hxn : 0 ≤ |x| := abs_nonneg x
  have hξn : 0 ≤ |ξ| := abs_nonneg ξ
  have e3 : |x * ξ| ^ 3 = |x| ^ 3 * |ξ| ^ 3 := by rw [abs_mul, mul_pow]
  have e4 : x ^ 4 = |x| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have e5 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have : |x| ^ 4 ≤ |x| ^ 3 := pow_le_pow_of_le_one hxn hx1 (by norm_num)
  calc _ ≤ |x * ξ| ^ 3 + 3 * ξ ^ 2 * (x ^ 4 / 96) := h3
    _ ≤ (20 * |x| * (|ξ| ^ 3 + ξ ^ 2)) * (x ^ 2 / 20) := by
        rw [e3, e4, e5]
        have hξ2 : ξ ^ 2 = |ξ| ^ 2 := (sq_abs ξ).symm
        rw [hξ2]
        have hx3 : 0 ≤ |x| ^ 3 := by positivity
        have hxx : |x| ^ 2 * |x| = |x| ^ 3 := by ring
        nlinarith [mul_nonneg (pow_nonneg hξn 2) hx3, pow_nonneg hξn 3, mul_nonneg (pow_nonneg hξn 3) hx3,
          mul_nonneg (pow_nonneg hξn 2) (pow_nonneg hxn 4), this]
    _ ≤ (20 * |x| * (|ξ| ^ 3 + ξ ^ 2)) * Kk x := by gcongr

theorem Gfun_cont (ξ : ℝ) : Continuous (Gfun ξ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Metric.continuousAt_iff]
    intro ε hε
    set M : ℝ := 20 * (|ξ| ^ 3 + ξ ^ 2) + 1 with hM
    have hMpos : 0 < M := by positivity
    refine ⟨min (min (1 / 2) (1 / (|ξ| + 1))) (ε / (2 * M)), by positivity, fun y hy => ?_⟩
    rw [dist_zero_right] at *
    by_cases hy0 : y = 0
    · subst hy0; simpa using hε
    have hy' : |y| < min (min (1 / 2) (1 / (|ξ| + 1))) (ε / (2 * M)) := by simpa [Real.dist_eq] using hy
    have h1 : |y| ≤ 1 / 2 := (hy'.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
    have h2 : |y| < 1 / (|ξ| + 1) := hy'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : |y| < ε / (2 * M) := hy'.trans_le (min_le_right _ _)
    have hξy : |y * ξ| ≤ 1 := by
      rw [abs_mul]
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |ξ| + 1)).1 h2
      nlinarith [abs_nonneg ξ, abs_nonneg y]
    have := Gfun_near ξ y hy0 h1 hξy
    rw [dist_eq_norm]
    refine this.trans_lt ?_
    have h4 : 20 * |y| * (|ξ| ^ 3 + ξ ^ 2) ≤ M * |y| := by rw [hM]; nlinarith [abs_nonneg y]
    have h5 : M * |y| < M * (ε / (2 * M)) := by gcongr
    have h6 : M * (ε / (2 * M)) = ε / 2 := by field_simp
    linarith
  · have hcont : ContinuousAt (fun y => cchi ξ y / (Kk y : ℂ)) x := by
      refine ContinuousAt.div (cchi_cont ξ).continuousAt
        (Complex.continuous_ofReal.comp Kk_cont).continuousAt ?_
      exact_mod_cast (Kk_pos hx).ne'
    refine hcont.congr ?_
    have : ∀ᶠ y in 𝓝 x, y ≠ 0 := isOpen_ne.mem_nhds hx
    filter_upwards [this] with y hy
    simp [Gfun, hy]

open scoped ENNReal NNReal
theorem finite_measure_limit (Λ : ℕ → Measure ℝ) [hΛ : ∀ n, IsFiniteMeasure (Λ n)] (c : ℝ) (hc : 0 < c)
    (hD : ∀ n, (Λ n).real Set.univ ≤ c)
    (htight : ∀ ε > 0, ∃ R : ℝ, 0 < R ∧ ∀ n, (Λ n).real {x : ℝ | R ≤ |x|} ≤ ε) :
    ∃ (φ : ℕ → ℕ) (L : Measure ℝ), StrictMono φ ∧ IsFiniteMeasure L ∧
      ∀ G : ℝ → ℂ, Continuous G → (∃ B : ℝ, ∀ x, ‖G x‖ ≤ B) →
        Tendsto (fun k => ∫ x, G x ∂(Λ (φ k))) atTop (𝓝 (∫ x, G x ∂L)) := by
  set m : ℕ → ℝ := fun n => (Λ n).real Set.univ with hm
  have hm0 : ∀ n, 0 ≤ m n := fun n => measureReal_nonneg
  -- the probability measures Q n
  let Q : ℕ → Measure ℝ := fun n =>
    ENNReal.ofReal (1 / c) • (Λ n + ENNReal.ofReal (c - m n) • Measure.dirac (0 : ℝ))
  have hQuniv : ∀ n, Q n Set.univ = 1 := by
    intro n
    simp only [Q, Measure.smul_apply, Measure.add_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _)]
    have h1 : Λ n Set.univ = ENNReal.ofReal (m n) := by
      simp only [hm, Measure.real]; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [h1, mul_one, ← ENNReal.ofReal_add (hm0 n) (by linarith [hD n]), ← ENNReal.ofReal_mul (by positivity)]
    have : 1 / c * (m n + (c - m n)) = 1 := by field_simp; ring
    rw [this]; simp
  have hQprob : ∀ n, IsProbabilityMeasure (Q n) := fun n => ⟨hQuniv n⟩
  let P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨Q n, hQprob n⟩
  have hPcoe : ∀ n, (P n : Measure ℝ) = Q n := fun n => rfl
  -- tightness
  have htightP : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun μ _ => by simp [hεtop]⟩
    · have hε0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
      obtain ⟨R, hR, hRt⟩ := htight (c * ε.toReal) (by positivity)
      refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
      rintro μ ⟨ν, ⟨n, rfl⟩, rfl⟩
      have hsub : (Set.Icc (-R) R)ᶜ ⊆ {x : ℝ | R ≤ |x|} := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
        simp only [Set.mem_setOf_eq]
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have h0 : (0 : ℝ) ∈ Set.Icc (-R) R := ⟨by linarith, hR.le⟩
      have h0' : (0 : ℝ) ∉ (Set.Icc (-R) R)ᶜ := by simpa using h0
      have hd : (Measure.dirac (0 : ℝ)) (Set.Icc (-R) R)ᶜ = 0 := by
        rw [Measure.dirac_apply' _ isClosed_Icc.measurableSet.compl, Set.indicator_of_notMem h0']
      have hQK : (Q n) (Set.Icc (-R) R)ᶜ = ENNReal.ofReal (1 / c) * Λ n (Set.Icc (-R) R)ᶜ := by
        simp [Q, hd]
      show (Q n) (Set.Icc (-R) R)ᶜ ≤ ε
      rw [hQK]
      have h1 : Λ n (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal (c * ε.toReal) := by
        calc Λ n (Set.Icc (-R) R)ᶜ ≤ Λ n {x : ℝ | R ≤ |x|} := measure_mono hsub
          _ = ENNReal.ofReal ((Λ n).real {x : ℝ | R ≤ |x|}) := by
              simp only [Measure.real]; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
          _ ≤ ENNReal.ofReal (c * ε.toReal) := ENNReal.ofReal_le_ofReal (hRt n)
      calc ENNReal.ofReal (1 / c) * Λ n (Set.Icc (-R) R)ᶜ
          ≤ ENNReal.ofReal (1 / c) * ENNReal.ofReal (c * ε.toReal) := by gcongr
        _ = ENNReal.ofReal (1 / c * (c * ε.toReal)) := (ENNReal.ofReal_mul (by positivity)).symm
        _ = ε := by
            have : 1 / c * (c * ε.toReal) = ε.toReal := by field_simp
            rw [this, ENNReal.ofReal_toReal hεtop]
  have hcomp : IsCompact (closure (Set.range P)) := isCompact_closure_of_isTightMeasureSet htightP
  have hmem : ∀ n, (P n, m n) ∈ closure (Set.range P) ×ˢ Set.Icc (0 : ℝ) c := fun n =>
    ⟨subset_closure ⟨n, rfl⟩, hm0 n, hD n⟩
  obtain ⟨⟨Pinf, minf⟩, ⟨hPin, hminf⟩, φ, hφ, hlim⟩ :=
    (hcomp.prod isCompact_Icc).tendsto_subseq hmem
  have hP : Tendsto (fun k => P (φ k)) atTop (𝓝 Pinf) := ((Prod.tendsto_iff _ (Pinf, minf)).1 hlim).1
  have hmlim : Tendsto (fun k => m (φ k)) atTop (𝓝 minf) := ((Prod.tendsto_iff _ (Pinf, minf)).1 hlim).2
  have hmin : 0 ≤ minf ∧ minf ≤ c := hminf
  -- positivity of the atom
  have hatom : ENNReal.ofReal ((c - minf) / c) ≤ (Pinf : Measure ℝ) {(0 : ℝ)} := by
    have h1 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hP (isClosed_singleton (x := (0 : ℝ)))
    have h2 : ∀ k, ENNReal.ofReal ((c - m (φ k)) / c) ≤ ((P (φ k) : ProbabilityMeasure ℝ) : Measure ℝ) {(0 : ℝ)} := by
      intro k
      show ENNReal.ofReal ((c - m (φ k)) / c) ≤ (Q (φ k)) {(0 : ℝ)}
      simp only [Q, Measure.smul_apply, Measure.add_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_singleton _), mul_one]
      calc ENNReal.ofReal ((c - m (φ k)) / c) = ENNReal.ofReal (1 / c) * ENNReal.ofReal (c - m (φ k)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
        _ ≤ ENNReal.ofReal (1 / c) * (Λ (φ k) {(0 : ℝ)} + ENNReal.ofReal (c - m (φ k))) := by gcongr; exact le_add_self
    have h3 : Tendsto (fun k => ENNReal.ofReal ((c - m (φ k)) / c)) atTop (𝓝 (ENNReal.ofReal ((c - minf) / c))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (((tendsto_const_nhds.sub hmlim).div_const c))
    calc ENNReal.ofReal ((c - minf) / c) = atTop.limsup (fun k => ENNReal.ofReal ((c - m (φ k)) / c)) := h3.limsup_eq.symm
      _ ≤ atTop.limsup (fun k => ((P (φ k) : ProbabilityMeasure ℝ) : Measure ℝ) {(0 : ℝ)}) := limsup_le_limsup (Eventually.of_forall h2)
      _ ≤ (Pinf : Measure ℝ) {(0 : ℝ)} := h1
  have hPreal : (c - minf) / c ≤ (Pinf : Measure ℝ).real {(0 : ℝ)} := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hatom
    rwa [ENNReal.toReal_ofReal (by apply div_nonneg <;> linarith)] at this
  set a : ℝ := c * (Pinf : Measure ℝ).real {(0 : ℝ)} - (c - minf) with ha
  have ha0 : 0 ≤ a := by
    have := (div_le_iff₀ hc).1 hPreal
    rw [ha]; nlinarith
  set L : Measure ℝ := ENNReal.ofReal c • (Pinf : Measure ℝ).restrict {(0 : ℝ)}ᶜ + ENNReal.ofReal a • Measure.dirac (0 : ℝ) with hL
  have fin1 : IsFiniteMeasure (ENNReal.ofReal c • (Pinf : Measure ℝ).restrict {(0 : ℝ)}ᶜ) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have fin2 : IsFiniteMeasure (ENNReal.ofReal a • Measure.dirac (0 : ℝ)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have : IsFiniteMeasure L := by rw [hL]; infer_instance
  refine ⟨φ, L, hφ, inferInstance, fun G hG ⟨B, hB⟩ => ?_⟩
  have hintG : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], Integrable G μ := fun μ _ =>
    Integrable.of_bound (C := B) hG.aestronglyMeasurable (Eventually.of_forall hB)
  let Gb : BoundedContinuousFunction ℝ ℂ := BoundedContinuousFunction.mkOfBound ⟨G, hG⟩ (2 * B) (by
    intro x y
    have := hB x; have := hB y
    simp only [ContinuousMap.coe_mk, dist_eq_norm]
    calc ‖G x - G y‖ ≤ ‖G x‖ + ‖G y‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith)
  have hGb : ∀ x, Gb x = G x := fun x => rfl
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hP Gb
  simp only [hGb] at hweak
  -- formula for ∫ G dΛ n
  have hform : ∀ n, ∫ x, G x ∂(Λ n) = (c : ℂ) * ∫ x, G x ∂(Q n) - ((c - m n : ℝ) : ℂ) * G 0 := by
    intro n
    have hq : ∫ x, G x ∂(Q n) = (1 / c : ℝ) • (∫ x, G x ∂(Λ n) + (c - m n : ℝ) • G 0) := by
      simp only [Q]
      rw [integral_smul_measure, integral_add_measure (hintG (Λ n)) (by
        have : IsFiniteMeasure (ENNReal.ofReal (c - m n) • Measure.dirac (0 : ℝ)) :=
          Measure.smul_finite _ ENNReal.ofReal_ne_top
        exact hintG _), integral_smul_measure, integral_dirac]
      rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by linarith [hD n])]
    rw [hq]
    simp only [Complex.real_smul]
    push_cast
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
    ring
  -- formula for ∫ G dL
  have hLform : ∫ x, G x ∂L = (c : ℂ) * ∫ x, G x ∂(Pinf : Measure ℝ) - ((c - minf : ℝ) : ℂ) * G 0 := by
    rw [hL, integral_add_measure (by
        exact hintG _) (by
        exact hintG _), integral_smul_measure, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal ha0]
    have hsplit := integral_add_compl (measurableSet_singleton (0 : ℝ)) (hintG (Pinf : Measure ℝ))
    rw [integral_singleton] at hsplit
    simp only [Complex.real_smul] at hsplit ⊢
    have : ∫ x in ({(0 : ℝ)}ᶜ), G x ∂(Pinf : Measure ℝ) = ∫ x, G x ∂(Pinf : Measure ℝ) - ((Pinf : Measure ℝ).real {(0 : ℝ)} : ℂ) * G 0 := by
      rw [← hsplit]; ring
    rw [this, ha]
    push_cast
    ring
  simp_rw [hform, hLform]
  have h1 : Tendsto (fun k => ∫ x, G x ∂(Q (φ k))) atTop (𝓝 (∫ x, G x ∂(Pinf : Measure ℝ))) := hweak
  have h2 : Tendsto (fun k => ((c - m (φ k) : ℝ) : ℂ)) atTop (𝓝 ((c - minf : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hmlim)
  exact (h1.const_mul (c : ℂ)).sub (h2.mul_const (G 0))


open LevyFoundations in
noncomputable def wfun (x : ℝ) : ℝ := x * (chi x - (if |x| < 1 then 1 else 0))

theorem wfun_meas : Measurable wfun := by
  unfold wfun
  refine Measurable.mul measurable_id (Measurable.sub chi_cont.measurable ?_)
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const

theorem wfun_bound (x : ℝ) : |wfun x| ≤ Set.indicator {x : ℝ | 1 / 2 ≤ |x|} (fun _ => (1 : ℝ)) x := by
  unfold wfun
  by_cases h : 1 / 2 ≤ |x|
  · rw [Set.indicator_of_mem (by exact h)]
    by_cases h1 : |x| < 1
    · simp only [h1, if_true]
      rw [abs_mul]
      have h2 := chi_nonneg x; have h3 := chi_le_one x
      have : |chi x - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg x, abs_nonneg (chi x - 1)]
    · simp only [h1, if_false, sub_zero]
      rw [chi_of_ge_one (not_lt.1 h1)]; simp
  · rw [Set.indicator_of_notMem (by exact h)]
    have h1 : |x| < 1 / 2 := not_le.1 h
    rw [chi_of_le_half h1.le]
    have : |x| < 1 := by linarith
    simp [this]

open LevyFoundations in
theorem wfun_integrable (η : Measure ℝ) (hη : isLevyMeasure η) : Integrable wfun η := by
  have hfin : η {x : ℝ | 1 / 2 ≤ |x|} < ⊤ := levy_finite_tail η hη (by norm_num)
  have hset : MeasurableSet {x : ℝ | 1 / 2 ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
  have hint : Integrable (Set.indicator {x : ℝ | 1 / 2 ≤ |x|} (fun _ => (1 : ℝ))) η :=
    (integrable_indicator_iff hset).2 (integrableOn_const (hs := hfin.ne))
  exact Integrable.mono' hint wfun_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact wfun_bound x)

open LevyFoundations in
theorem cchi_eq (ξ x : ℝ) :
    cchi ξ x = compensatedIntegrand ξ x - Complex.I * ξ * (wfun x : ℂ) := by
  unfold cchi compensatedIntegrand wfun
  by_cases hx : |x| < 1
  · simp [hx]; ring
  · simp [hx]; ring

open LevyFoundations in
theorem cchi_integrable (η : Measure ℝ) (hη : isLevyMeasure η) (ξ : ℝ) :
    Integrable (fun x => cchi ξ x) η := by
  have h1 := comp_integrable η hη ξ
  have h2 : Integrable (fun x : ℝ => Complex.I * ξ * (wfun x : ℂ)) η := by
    have := (wfun_integrable η hη).ofReal (𝕜 := ℂ)
    exact this.const_mul (Complex.I * ξ)
  simp_rw [cchi_eq]
  exact h1.sub h2

open LevyFoundations in
noncomputable def bchi (T : LevyKhintchineTriple) : ℝ := T.drift + ∫ x, wfun x ∂T.levyMeasure

open LevyFoundations in
theorem exponent_chi (T : LevyKhintchineTriple) (ξ : ℝ) :
    exponent T ξ = (bchi T : ℂ) * ξ * Complex.I - (T.gaussianVariance : ℝ) * ξ ^ 2 / 2
      + ∫ x, cchi ξ x ∂T.levyMeasure := by
  have hη := T.levyMeasure_condition
  have e1 : ∫ x, cchi ξ x ∂T.levyMeasure
      = ∫ x, compensatedIntegrand ξ x ∂T.levyMeasure - Complex.I * ξ * ((∫ x, wfun x ∂T.levyMeasure : ℝ) : ℂ) := by
    have hA : Integrable (fun x : ℝ => compensatedIntegrand ξ x) T.levyMeasure := comp_integrable _ hη ξ
    have hB : Integrable (fun x : ℝ => Complex.I * ξ * (wfun x : ℂ)) T.levyMeasure :=
      ((wfun_integrable _ hη).ofReal (𝕜 := ℂ)).const_mul (Complex.I * ξ)
    have e2 : (fun x : ℝ => cchi ξ x) = fun x => compensatedIntegrand ξ x - Complex.I * ξ * (wfun x : ℂ) :=
      funext (cchi_eq ξ)
    rw [e2, integral_sub hA hB, integral_const_mul, integral_complex_ofReal]
  rw [e1]
  unfold exponent bchi
  push_cast
  ring

open LevyFoundations in
noncomputable def LamM (T : LevyKhintchineTriple) : Measure ℝ :=
  ENNReal.ofReal ((T.gaussianVariance : ℝ) / 6) • Measure.dirac (0 : ℝ)
    + T.levyMeasure.withDensity (fun x => ENNReal.ofReal (Kk x))

open LevyFoundations in
theorem LamM_finite (T : LevyKhintchineTriple) : IsFiniteMeasure (LamM T) := by
  have h1 : IsFiniteMeasure (ENNReal.ofReal ((T.gaussianVariance : ℝ) / 6) • Measure.dirac (0 : ℝ)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hi := Kk_integrable T.levyMeasure T.levyMeasure_condition 1
  simp only [one_mul] at hi
  have h2 : IsFiniteMeasure (T.levyMeasure.withDensity (fun x => ENNReal.ofReal (Kk x))) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  unfold LamM; infer_instance

open LevyFoundations in
theorem LamM_integral (T : LevyKhintchineTriple) (G : ℝ → ℂ) (hG : Measurable G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) :
    ∫ x, G x ∂(LamM T) = (((T.gaussianVariance : ℝ) / 6 : ℝ) : ℂ) * G 0
      + ∫ x, ((Kk x : ℝ) : ℂ) * G x ∂T.levyMeasure := by
  haveI := LamM_finite T
  have hint : Integrable G (LamM T) := Integrable.of_bound (C := B) hG.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hs : IsFiniteMeasure (ENNReal.ofReal ((T.gaussianVariance : ℝ) / 6) • Measure.dirac (0 : ℝ)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hi := Kk_integrable T.levyMeasure T.levyMeasure_condition 1
  simp only [one_mul] at hi
  have hw : IsFiniteMeasure (T.levyMeasure.withDensity (fun x => ENNReal.ofReal (Kk x))) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  unfold LamM at hint ⊢
  rw [integral_add_measure (Integrable.of_bound (C := B) hG.aestronglyMeasurable (Filter.Eventually.of_forall hB))
    (Integrable.of_bound (C := B) hG.aestronglyMeasurable (Filter.Eventually.of_forall hB)),
    integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul₀ (Kk_cont.measurable.ennreal_ofReal.aemeasurable)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (Kk_nonneg x)]

open LevyFoundations in
theorem LamM_real_univ (T : LevyKhintchineTriple) :
    (LamM T).real Set.univ = (T.gaussianVariance : ℝ) / 6 + ∫ x, Kk x ∂T.levyMeasure := by
  haveI := LamM_finite T
  have hi := Kk_integrable T.levyMeasure T.levyMeasure_condition 1
  simp only [one_mul] at hi
  unfold LamM Measure.real
  rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul, mul_one]
  have : ∫⁻ x, ENNReal.ofReal (Kk x) ∂T.levyMeasure = ENNReal.ofReal (∫ x, Kk x ∂T.levyMeasure) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall Kk_nonneg)).symm
  rw [this, ← ENNReal.ofReal_add (by positivity) (integral_nonneg (f := Kk) fun x => Kk_nonneg x),
    ENNReal.toReal_ofReal (by have := integral_nonneg (μ := T.levyMeasure) (f := Kk) (fun x => Kk_nonneg x); positivity)]

theorem finite_tail_small (μ : Measure ℝ) [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ R' ≥ R, μ.real {x : ℝ | R' ≤ |x|} ≤ ε := by
  have hanti : Antitone (fun k : ℕ => {x : ℝ | (k : ℝ) ≤ |x|}) := by
    intro a b hab x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hmeas : ∀ k : ℕ, NullMeasurableSet {x : ℝ | (k : ℝ) ≤ |x|} μ := fun k =>
    (measurableSet_le measurable_const (by fun_prop)).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  have hempty : ⋂ k : ℕ, {x : ℝ | (k : ℝ) ≤ |x|} = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    exact ⟨k, hk⟩
  rw [hempty, measure_empty] at hlim
  have hreal : Tendsto (fun k : ℕ => μ.real {x : ℝ | (k : ℝ) ≤ |x|}) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa [Measure.real, Function.comp_def] using this
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hreal) ε hε
  refine ⟨(K : ℝ) + 1, by positivity, fun R' hR' => ?_⟩
  have hk := hK K le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hk
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hk.le
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  linarith

theorem tail_all (ν : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (ν n)]
    (h : ∀ ε > 0, ∃ R : ℝ, 0 < R ∧ ∃ N : ℕ, ∀ n ≥ N, (ν n).real {x : ℝ | R ≤ |x|} ≤ ε) :
    ∀ ε > 0, ∃ R : ℝ, 0 < R ∧ ∀ n, (ν n).real {x : ℝ | R ≤ |x|} ≤ ε := by
  intro ε hε
  obtain ⟨R0, hR0, N, hN⟩ := h ε hε
  choose Rn hRn hRn' using fun n => finite_tail_small (ν n) ε hε
  refine ⟨max R0 (∑ n ∈ Finset.range N, Rn n), lt_max_of_lt_left hR0, fun n => ?_⟩
  by_cases hn : n < N
  · have hle : Rn n ≤ ∑ m ∈ Finset.range N, Rn m :=
      Finset.single_le_sum (f := Rn) (fun m _ => (hRn m).le) (Finset.mem_range.2 hn)
    exact hRn' n _ (hle.trans (le_max_right _ _))
  · rw [not_lt] at hn
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hN n hn)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact (le_max_left _ _).trans hx

open LevyFoundations in
theorem LamM_tail (T : LevyKhintchineTriple) {R : ℝ} (hR : 0 < R) :
    (LamM T).real {x : ℝ | R ≤ |x|} ≤ 2 * (T.levyMeasure {x : ℝ | R ≤ |x|}).toReal := by
  haveI := LamM_finite T
  have hset : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
  have hfin : T.levyMeasure {x : ℝ | R ≤ |x|} < ⊤ := levy_finite_tail _ T.levyMeasure_condition hR
  have h0 : (0 : ℝ) ∉ {x : ℝ | R ≤ |x|} := by simpa using hR
  have h1 : LamM T {x : ℝ | R ≤ |x|} ≤ 2 * T.levyMeasure {x : ℝ | R ≤ |x|} := by
    unfold LamM
    rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hset, Set.indicator_of_notMem h0,
      smul_zero, zero_add, withDensity_apply _ hset]
    calc ∫⁻ x in {x : ℝ | R ≤ |x|}, ENNReal.ofReal (Kk x) ∂T.levyMeasure
        ≤ ∫⁻ x in {x : ℝ | R ≤ |x|}, 2 ∂T.levyMeasure :=
          lintegral_mono fun x => by
            have := Kk_le_two x
            simpa using ENNReal.ofReal_le_ofReal this
      _ = 2 * T.levyMeasure {x : ℝ | R ≤ |x|} := by
          rw [setLIntegral_const]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hfin.ne) h1
  simpa [Measure.real, ENNReal.toReal_mul] using this

open LevyFoundations in
theorem build_triple (L : Measure ℝ) [IsFiniteMeasure L] (b : ℝ) :
    ∃ U : LevyKhintchineTriple, ∀ ξ : ℝ,
      (b : ℂ) * ξ * Complex.I + ∫ x, Gfun ξ x ∂L = exponent U ξ := by
  set η : Measure ℝ := (L.restrict {(0 : ℝ)}ᶜ).withDensity (fun x => ENNReal.ofReal (1 / Kk x)) with hη
  have hLevy : isLevyMeasure η := by
    refine ⟨?_, ?_⟩
    · rw [hη, withDensity_apply _ (measurableSet_singleton _)]
      simp
    · have hmK : Measurable (fun x : ℝ => ENNReal.ofReal (1 / Kk x)) :=
        ENNReal.measurable_ofReal.comp (measurable_const.div Kk_cont.measurable)
      have hmg : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.min (by fun_prop))
      rw [hη, lintegral_withDensity_eq_lintegral_mul (L.restrict {(0 : ℝ)}ᶜ) hmK hmg]
      calc _ ≤ ∫⁻ x, 20 ∂(L.restrict {(0 : ℝ)}ᶜ) := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with x hx
            have hx0 : x ≠ 0 := hx
            have hK := Kk_pos hx0
            have := Kk_lower x
            simp only [Pi.mul_apply]
            rw [← ENNReal.ofReal_mul (by positivity)]
            have : 1 / Kk x * min 1 (x ^ 2) ≤ 20 := by
              rw [one_div, inv_mul_le_iff₀ hK]; linarith
            calc ENNReal.ofReal (1 / Kk x * min 1 (x ^ 2)) ≤ ENNReal.ofReal 20 := ENNReal.ofReal_le_ofReal this
              _ = 20 := by simp
        _ = 20 * (L.restrict {(0 : ℝ)}ᶜ) Set.univ := by rw [lintegral_const]
        _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)
  have hGint : ∀ ξ : ℝ, Integrable (Gfun ξ) L := fun ξ =>
    Integrable.of_bound (C := 80 * (2 + |ξ|) + 60 * ξ ^ 2 + 3 * ξ ^ 2) (Gfun_cont ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => Gfun_bound ξ x)
  have hKpos : ∀ᵐ x ∂(L.restrict {(0 : ℝ)}ᶜ), x ≠ 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with x hx using hx
  have hint_cchi : ∀ ξ : ℝ, ∫ x, cchi ξ x ∂η = ∫ x in ({(0 : ℝ)}ᶜ), Gfun ξ x ∂L := by
    intro ξ
    have hmK : Measurable (fun x : ℝ => ENNReal.ofReal (1 / Kk x)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.div Kk_cont.measurable)
    rw [hη, integral_withDensity_eq_integral_toReal_smul₀ hmK.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hKpos] with x hx
    have hK := Kk_pos hx
    simp only [Complex.real_smul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hGx : Gfun ξ x = cchi ξ x / (Kk x : ℂ) := by simp [Gfun, hx]
    rw [hGx]
    have : (Kk x : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    push_cast
    field_simp
  refine ⟨⟨b - ∫ x, wfun x ∂η, (6 * L.real {(0 : ℝ)}).toNNReal, η, hLevy⟩, fun ξ => ?_⟩
  have hs : (((6 * L.real {(0 : ℝ)}).toNNReal : ℝ≥0) : ℝ) = 6 * L.real {(0 : ℝ)} :=
    Real.coe_toNNReal _ (by have := measureReal_nonneg (μ := L) (s := {(0 : ℝ)}); positivity)
  rw [exponent_chi]
  simp only [bchi, sub_add_cancel]
  rw [hs]
  have hsplit := integral_add_compl (measurableSet_singleton (0 : ℝ)) (hGint ξ)
  rw [integral_singleton, hint_cchi ξ] at *
  simp only [Complex.real_smul] at hsplit
  have hG0 : Gfun ξ 0 = ((-3 * ξ ^ 2 : ℝ) : ℂ) := by simp [Gfun]
  rw [← hsplit, hG0]
  push_cast
  ring

open LevyFoundations in
theorem exponent_via_G (T : LevyKhintchineTriple) (ξ : ℝ) :
    exponent T ξ = (bchi T : ℂ) * ξ * Complex.I + ∫ x, Gfun ξ x ∂(LamM T) := by
  rw [LamM_integral T (Gfun ξ) (Gfun_cont ξ).measurable _ (fun x => Gfun_bound ξ x), exponent_chi]
  have h1 : ∫ x, ((Kk x : ℝ) : ℂ) * Gfun ξ x ∂T.levyMeasure = ∫ x, cchi ξ x ∂T.levyMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_comm]; exact Gfun_mul ξ x
  have hG0 : Gfun ξ 0 = ((-3 * ξ ^ 2 : ℝ) : ℂ) := by simp [Gfun]
  rw [h1, hG0]
  push_cast
  ring

open LevyFoundations in
theorem exponent_limit_main (T : ℕ → LevyKhintchineTriple) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hlim : ∀ ξ : ℝ, Tendsto (fun n => exponent (T n) ξ) atTop (𝓝 (ψ ξ))) :
    ∃ U : LevyKhintchineTriple, ∀ ξ : ℝ, ψ ξ = exponent U ξ := by
  obtain ⟨C, N0, hC⟩ := mass_bound T ψ hψ hlim
  set T' : ℕ → LevyKhintchineTriple := fun k => T (k + N0) with hT'
  have hlim' : ∀ ξ : ℝ, Tendsto (fun k => exponent (T' k) ξ) atTop (𝓝 (ψ ξ)) :=
    fun ξ => (hlim ξ).comp (tendsto_add_atTop_nat N0)
  set c : ℝ := max C 1 with hc
  have hcpos : 0 < c := lt_max_of_lt_right one_pos
  haveI hfin : ∀ k, IsFiniteMeasure (LamM (T' k)) := fun k => LamM_finite _
  have hmass : ∀ k, (LamM (T' k)).real Set.univ ≤ c := by
    intro k
    rw [LamM_real_univ]
    exact (hC (k + N0) (by omega)).trans (le_max_left _ _)
  have htight : ∀ ε > 0, ∃ R : ℝ, 0 < R ∧ ∀ k, (LamM (T' k)).real {x : ℝ | R ≤ |x|} ≤ ε := by
    refine tail_all (fun k => LamM (T' k)) ?_
    intro ε hε
    obtain ⟨R, hR, N, hN⟩ := tail_bound T' ψ hψ hlim' (ε / 2) (by positivity)
    refine ⟨R, hR, N, fun n hn => ?_⟩
    have := LamM_tail (T' n) hR
    have := hN n hn
    linarith
  obtain ⟨φ, L, hφ, hLfin, hconv⟩ := finite_measure_limit (fun k => LamM (T' k)) c hcpos hmass htight
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hE : ∀ ξ, Tendsto (fun k => exponent (T' (φ k)) ξ) atTop (𝓝 (ψ ξ)) := fun ξ => (hlim' ξ).comp hφt
  have hH : ∀ ξ, Tendsto (fun k => ∫ x, Gfun ξ x ∂(LamM (T' (φ k)))) atTop (𝓝 (∫ x, Gfun ξ x ∂L)) :=
    fun ξ => hconv (Gfun ξ) (Gfun_cont ξ) ⟨_, fun x => Gfun_bound ξ x⟩
  -- the drift converges
  have hb : ∀ k, bchi (T' (φ k)) = (exponent (T' (φ k)) 1).im - (∫ x, Gfun 1 x ∂(LamM (T' (φ k)))).im := by
    intro k
    have := congrArg Complex.im (exponent_via_G (T' (φ k)) 1)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at this
    simp at this
    linarith
  have hbl : Tendsto (fun k => bchi (T' (φ k))) atTop (𝓝 ((ψ 1).im - (∫ x, Gfun 1 x ∂L).im)) := by
    simp_rw [hb]
    exact ((Complex.continuous_im.tendsto _).comp (hE 1)).sub ((Complex.continuous_im.tendsto _).comp (hH 1))
  set b : ℝ := (ψ 1).im - (∫ x, Gfun 1 x ∂L).im with hbdef
  have hrep : ∀ ξ : ℝ, ψ ξ = (b : ℂ) * ξ * Complex.I + ∫ x, Gfun ξ x ∂L := by
    intro ξ
    have h1 : Tendsto (fun k => (bchi (T' (φ k)) : ℂ) * ξ * Complex.I + ∫ x, Gfun ξ x ∂(LamM (T' (φ k)))) atTop
        (𝓝 ((b : ℂ) * ξ * Complex.I + ∫ x, Gfun ξ x ∂L)) := by
      have hb' : Tendsto (fun k => (bchi (T' (φ k)) : ℂ)) atTop (𝓝 (b : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp hbl
      exact ((hb'.mul_const (ξ : ℂ)).mul_const Complex.I).add (hH ξ)
    have h2 : Tendsto (fun k => (bchi (T' (φ k)) : ℂ) * ξ * Complex.I + ∫ x, Gfun ξ x ∂(LamM (T' (φ k)))) atTop (𝓝 (ψ ξ)) := by
      refine (hE ξ).congr fun k => ?_
      exact exponent_via_G _ ξ
    exact tendsto_nhds_unique h2 h1
  obtain ⟨U, hU⟩ := build_triple L b
  exact ⟨U, fun ξ => (hrep ξ).trans (hU ξ)⟩

end LevyLimitAux

theorem solution
    (T : ℕ → LevyFoundations.LevyKhintchineTriple) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hlim : ∀ ξ : ℝ, Filter.Tendsto (fun n => LevyFoundations.exponent (T n) ξ) Filter.atTop (nhds (ψ ξ))) :
    ∃ U : LevyFoundations.LevyKhintchineTriple, ∀ ξ : ℝ, ψ ξ = LevyFoundations.exponent U ξ :=
  LevyLimitAux.exponent_limit_main T ψ hψ hlim
