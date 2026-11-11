-- Prove2me | solution 2 for levy_foundations_semigroup_exponent_is_levyKhintchine
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:38:13.146195+00:00
-- url     : https://prove2.me/submissions/b4f6da8f-c874-432b-bb40-5c9f1ff3b830

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_exponent_pointwise_limit

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped NNReal ENNReal

/-- compound Poisson triplet of mass `c` built from a probability measure `ν`. -/
private theorem cp_triplet (ν : Measure ℝ) [IsProbabilityMeasure ν] (c : ℝ≥0) :
    ∃ T : LevyFoundations.LevyKhintchineTriple, ∀ ξ : ℝ,
      LevyFoundations.exponent T ξ = (c : ℂ) * (charFun ν ξ - 1) := by
  set η : Measure ℝ := c • ν.restrict {0}ᶜ with hη
  have hη0 : η {0} = 0 := by simp [hη]
  have hηfin : IsFiniteMeasure η := by
    rw [hη]; infer_instance
  have hηL : LevyFoundations.isLevyMeasure η := by
    refine ⟨hη0, ?_⟩
    calc ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂η ≤ ∫⁻ x, 1 ∂η := by
          refine lintegral_mono fun x => ?_
          simp
      _ = η Set.univ := by simp
      _ < ⊤ := measure_lt_top _ _
  set b : ℝ := (c : ℝ) * ∫ x in {x : ℝ | |x| < 1}, x ∂ν with hb
  refine ⟨⟨b, 0, η, hηL⟩, fun ξ => ?_⟩
  -- integrability facts
  have hcomp_meas : ∀ ξ : ℝ, Measurable (fun x : ℝ => LevyFoundations.compensatedIntegrand ξ x) := by
    intro ξ
    unfold LevyFoundations.compensatedIntegrand
    refine Measurable.sub (Measurable.sub (by fun_prop) measurable_const) ?_
    refine Measurable.mul (by fun_prop) ?_
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const
  have hcomp_zero : LevyFoundations.compensatedIntegrand ξ 0 = 0 := by
    simp [LevyFoundations.compensatedIntegrand]
  have h1 : ∫ x, LevyFoundations.compensatedIntegrand ξ x ∂η
      = c • ∫ x, LevyFoundations.compensatedIntegrand ξ x ∂(ν.restrict {0}ᶜ) := by
    rw [hη, integral_smul_nnreal_measure]
  have h2 : ∫ x, LevyFoundations.compensatedIntegrand ξ x ∂(ν.restrict {0}ᶜ)
      = ∫ x, LevyFoundations.compensatedIntegrand ξ x ∂ν := by
    have := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν) (s := ({0}ᶜ : Set ℝ))
      (f := fun x => LevyFoundations.compensatedIntegrand ξ x) (fun x hx => by
        have : x = 0 := by simpa using hx
        subst this; exact hcomp_zero)
    exact this
  -- split the integral over ν
  have he : Integrable (fun x : ℝ => Complex.exp ((x : ℂ) * ↑ξ * Complex.I)) ν := by
    refine Integrable.of_bound (C := 1) (by fun_prop : Continuous fun x : ℝ => Complex.exp ((x : ℂ) * ↑ξ * Complex.I)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have e : (x : ℂ) * ↑ξ * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hint1 : Integrable (fun x : ℝ => Complex.exp ((x : ℂ) * ↑ξ * Complex.I) - 1) ν :=
    he.sub (integrable_const _)
  have hint2 : Integrable (fun x : ℝ => (x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then 1 else 0)) ν := by
    refine Integrable.of_bound (C := |ξ|) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Measurable.mul (by fun_prop) (Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const)).aestronglyMeasurable
    · by_cases hx : |x| < 1
      · simp only [hx, if_true, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
        calc |x| * |ξ| ≤ 1 * |ξ| := by gcongr
          _ = |ξ| := one_mul _
      · simp [hx]
  have hE : ∫ x, Complex.exp ((x : ℂ) * ↑ξ * Complex.I) ∂ν = charFun ν ξ := by
    rw [charFun_apply_real]; congr 1; ext x; ring_nf
  have hB : ∫ x, (x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then 1 else 0) ∂ν
      = (ξ : ℂ) * Complex.I * ((∫ x in {x : ℝ | |x| < 1}, x ∂ν : ℝ) : ℂ) := by
    have hm : MeasurableSet {x : ℝ | |x| < 1} := measurableSet_lt (by fun_prop) measurable_const
    have e : (fun x : ℝ => (x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then 1 else 0))
        = fun x => ((ξ : ℂ) * Complex.I) * (((Set.indicator {x : ℝ | |x| < 1} (fun x => x) x : ℝ)) : ℂ) := by
      ext x
      by_cases hx : |x| < 1
      · simp [Set.indicator, hx]; ring
      · simp [Set.indicator, hx]
    rw [e, integral_const_mul, integral_complex_ofReal, integral_indicator hm]
  have hsplit : ∫ x, LevyFoundations.compensatedIntegrand ξ x ∂ν
      = (charFun ν ξ - 1) - (ξ : ℂ) * Complex.I * ((∫ x in {x : ℝ | |x| < 1}, x ∂ν : ℝ) : ℂ) := by
    unfold LevyFoundations.compensatedIntegrand
    rw [integral_sub hint1 hint2, integral_sub he (integrable_const _), hE, hB]
    simp
  have hfin : LevyFoundations.exponent ⟨b, 0, η, hηL⟩ ξ = (c : ℂ) * (charFun ν ξ - 1) := by
    unfold LevyFoundations.exponent
    simp only [NNReal.coe_zero, Complex.ofReal_zero]
    rw [h1, h2, hsplit, hb]
    rw [NNReal.smul_def, Complex.real_smul]
    push_cast
    ring
  exact hfin

private theorem cp_tendsto (w : ℂ) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) * (Complex.exp (w / ((n : ℂ) + 1)) - 1)) atTop (𝓝 w) := by
  by_cases hw : w = 0
  · subst hw; simp
  have hz : Tendsto (fun n : ℕ => w / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [Function.comp_def] using this
      have h2 := h1.const_mul w
      simp only [mul_zero] at h2
      refine h2.congr fun n => ?_
      push_cast
      ring
    · have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simpa [this] using hw
  have hd := (Complex.hasDerivAt_exp 0).tendsto_slope_zero
  have hslope := hd.comp hz
  have key : ∀ n : ℕ, ((n : ℂ) + 1) * (Complex.exp (w / ((n : ℂ) + 1)) - 1)
      = w * ((w / ((n : ℂ) + 1))⁻¹ • (Complex.exp (0 + w / ((n : ℂ) + 1)) - Complex.exp 0)) := by
    intro n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [zero_add, Complex.exp_zero, smul_eq_mul]
    field_simp
  simp_rw [key]
  simpa using hslope.const_mul w


theorem solution
    (ψ : ℝ → ℂ)
    (hψ : Continuous ψ)
    (hsemigroup :
      ∀ t : ℝ, 0 ≤ t →
        ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, ψ ξ = LevyFoundations.exponent T ξ := by
  choose ν hνp hν using fun n : ℕ => hsemigroup (1 / ((n : ℝ) + 1)) (by positivity)
  have hT : ∀ n : ℕ, ∃ T : LevyFoundations.LevyKhintchineTriple, ∀ ξ : ℝ,
      LevyFoundations.exponent T ξ = (((n + 1 : ℝ≥0)) : ℂ) * (charFun (ν n) ξ - 1) := by
    intro n
    have := hνp n
    exact cp_triplet (ν n) (n + 1)
  choose T hT using hT
  refine levy_foundations_exponent_pointwise_limit T ψ hψ (fun ξ => ?_)
  have := cp_tendsto (ψ ξ)
  refine this.congr fun n => ?_
  rw [hT n ξ, hν n ξ]
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  congr 3
  field_simp
