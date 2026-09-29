-- Prove2me | solution 1 for exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/50939bc0-8ef1-5732-9097-5a7497161588

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq

set_option autoImplicit false

open MeasureTheory

open Set

private noncomputable def abelL : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ

private noncomputable def abelKer (t : ℝ) : ℝ := if t < 0 then 1 / Real.sqrt (-t) else 0

private theorem abelKer_of_neg {t : ℝ} (ht : t < 0) : abelKer t = 1 / Real.sqrt (-t) := if_pos ht

private theorem abelKer_of_nonneg {t : ℝ} (ht : 0 ≤ t) : abelKer t = 0 := if_neg (not_lt.2 ht)

private theorem abelKer_nonneg (t : ℝ) : 0 ≤ abelKer t := by
  unfold abelKer
  split_ifs
  · exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  · exact le_rfl

private theorem hasDerivAt_primitive_abelKer {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun x : ℝ => -2 * Real.sqrt (-x)) (abelKer t) t := by
  have h1 : HasDerivAt (fun x : ℝ => -x) (-1) t := (hasDerivAt_id t).neg
  have h2 := (h1.sqrt (by simpa using ht.ne)).const_mul (-2 : ℝ)
  have hpos : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  convert h2 using 1
  all_goals try rfl
  rw [abelKer_of_neg ht]
  field_simp

private theorem abelKer_integrableOn_Ioc_of_nonpos {a b : ℝ} (hb : b ≤ 0) : IntegrableOn abelKer (Ioc a b) := by
  rcases le_or_gt b a with hab | hab
  · rw [Ioc_eq_empty (not_lt.2 hab)]
    exact integrableOn_empty
  · refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun x : ℝ => -2 * Real.sqrt (-x)) ?_ ?_ ?_
    · exact (continuous_const.mul (Real.continuous_sqrt.comp continuous_neg)).continuousOn
    · intro x hx
      exact hasDerivAt_primitive_abelKer (by linarith [hx.2])
    · intro x _
      exact abelKer_nonneg x

private theorem abelKer_integrableOn_Ioi_zero : IntegrableOn abelKer (Ioi (0 : ℝ)) := by
  refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact (abelKer_of_nonneg (Set.mem_Ioi.1 ht).le).symm

private theorem abelKer_locallyIntegrable : LocallyIntegrable abelKer := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall (0 : ℝ)
  have hsub : k ⊆ Ioc (-R - 1) 0 ∪ Ioi 0 := by
    intro t htk
    have := hR htk
    rw [Real.closedBall_eq_Icc] at this
    by_cases ht : t ≤ 0
    · exact Or.inl ⟨by linarith [this.1], ht⟩
    · exact Or.inr (not_le.1 ht)
  exact ((abelKer_integrableOn_Ioc_of_nonpos le_rfl).union abelKer_integrableOn_Ioi_zero).mono_set hsub

private noncomputable def pairKer (η s ξ : ℝ) : ℝ := 1 / (Real.sqrt (s - ξ) * Real.sqrt (ξ - η))

private theorem pairKer_nonneg (η s ξ : ℝ) : 0 ≤ pairKer η s ξ :=
  div_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private noncomputable def pairPrim (η s ξ : ℝ) : ℝ := Real.arcsin ((2 * ξ - η - s) / (s - η))

private theorem continuous_pairPrim (η s : ℝ) : Continuous (pairPrim η s) := by
  unfold pairPrim
  exact Real.continuous_arcsin.comp (by fun_prop)

private theorem hasDerivAt_pairPrim {η s ξ : ℝ} (hη : η < ξ) (hs : ξ < s) :
    HasDerivAt (pairPrim η s) (pairKer η s ξ) ξ := by
  have hsη : 0 < s - η := by linarith
  have hu : HasDerivAt (fun x : ℝ => (2 * x - η - s) / (s - η)) (2 / (s - η)) ξ := by
    have : HasDerivAt (fun x : ℝ => 2 * x - η - s) 2 ξ := by
      simpa using (((hasDerivAt_id ξ).const_mul (2 : ℝ)).sub_const η).sub_const s
    simpa [div_eq_mul_inv] using this.mul_const (s - η)⁻¹
  have hA : 0 < s - ξ := by linarith
  have hB : 0 < ξ - η := by linarith
  have hne1 : (2 * ξ - η - s) / (s - η) ≠ -1 := by
    rw [Ne, div_eq_iff hsη.ne']
    intro h
    linarith
  have hne2 : (2 * ξ - η - s) / (s - η) ≠ 1 := by
    rw [Ne, div_eq_iff hsη.ne']
    intro h
    linarith
  have h := (Real.hasDerivAt_arcsin hne1 hne2).comp ξ hu
  have h' : HasDerivAt (pairPrim η s)
      (1 / Real.sqrt (1 - ((2 * ξ - η - s) / (s - η)) ^ 2) * (2 / (s - η))) ξ := h
  have hDne : s - η ≠ 0 := hsη.ne'

  have hsq : 1 - ((2 * ξ - η - s) / (s - η)) ^ 2 =
      (2 * Real.sqrt (s - ξ) * Real.sqrt (ξ - η) / (s - η)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    field
  have hroot : Real.sqrt (1 - ((2 * ξ - η - s) / (s - η)) ^ 2) =
      2 * Real.sqrt (s - ξ) * Real.sqrt (ξ - η) / (s - η) := by
    rw [hsq]
    exact Real.sqrt_sq
      (div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hsη.le)
  have hsA : Real.sqrt (s - ξ) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsB : Real.sqrt (ξ - η) ≠ 0 := (Real.sqrt_pos.2 hB).ne'
  refine h'.congr_deriv ?_
  rw [hroot]
  unfold pairKer
  field

private theorem pairPrim_right (η s : ℝ) (h : η < s) : pairPrim η s s = Real.pi / 2 := by
  unfold pairPrim
  have : (2 * s - η - s) / (s - η) = 1 := by
    rw [div_eq_one_iff_eq (sub_pos.2 h).ne']
    ring
  rw [this, Real.arcsin_one]

private theorem pairPrim_left (η s : ℝ) (h : η < s) : pairPrim η s η = -(Real.pi / 2) := by
  unfold pairPrim
  have : (2 * η - η - s) / (s - η) = -1 := by
    rw [div_eq_iff (sub_pos.2 h).ne']
    ring
  rw [this, Real.arcsin_neg_one]

private theorem pairKer_integrableOn (η s : ℝ) : IntegrableOn (pairKer η s) (Ioo η s) := by
  refine (intervalIntegral.integrableOn_deriv_of_nonneg (g := pairPrim η s) (continuous_pairPrim η s).continuousOn
    (fun x hx => hasDerivAt_pairPrim hx.1 hx.2) (fun x _ => pairKer_nonneg η s x)).mono_set Ioo_subset_Ioc_self

private theorem pairKer_integral {η s : ℝ} (h : η < s) : ∫ ξ in Ioo η s, pairKer η s ξ = Real.pi := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h.le]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.le (continuous_pairPrim η s).continuousOn
    (fun x hx => hasDerivAt_pairPrim hx.1 hx.2)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h.le).2
      (intervalIntegral.integrableOn_deriv_of_nonneg (continuous_pairPrim η s).continuousOn
        (fun x hx => hasDerivAt_pairPrim hx.1 hx.2) (fun x _ => pairKer_nonneg η s x)))]
  rw [pairPrim_right η s h, pairPrim_left η s h]
  ring

private noncomputable def pairKer2 (η : ℝ) (q : ℝ × ℝ) : ℝ := (Ioo η q.2).indicator (pairKer η q.2) q.1

private theorem measurable_pairKer2 (η : ℝ) : Measurable (pairKer2 η) := by
  have hS : MeasurableSet {q : ℝ × ℝ | η < q.1 ∧ q.1 < q.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter (measurableSet_lt measurable_fst measurable_snd)
  have hker : Measurable (fun q : ℝ × ℝ => pairKer η q.2 q.1) := by
    unfold pairKer
    exact measurable_const.div ((Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst)).mul
      (Real.continuous_sqrt.measurable.comp (measurable_fst.sub measurable_const)))
  have : pairKer2 η = {q : ℝ × ℝ | η < q.1 ∧ q.1 < q.2}.indicator (fun q => pairKer η q.2 q.1) := by
    funext q
    simp only [pairKer2, Set.indicator_apply, Set.mem_Ioo, Set.mem_setOf_eq]
  rw [this]
  exact hker.indicator hS

private theorem pairKer2_nonneg (η : ℝ) (q : ℝ × ℝ) : 0 ≤ pairKer2 η q := by
  unfold pairKer2 Set.indicator
  split_ifs
  · exact pairKer_nonneg _ _ _
  · exact le_rfl

private noncomputable def abelF (h : ℝ → ℂ) (η ξ s : ℝ) : ℂ := h s * ((pairKer2 η (ξ, s) : ℝ) : ℂ)

private theorem abelF_eq_of_not_lt (h : ℝ → ℂ) {η s : ℝ} (hηs : ¬ η < s) (ξ : ℝ) : abelF h η ξ s = 0 := by
  simp [abelF, pairKer2, Set.Ioo_eq_empty hηs]

private theorem abelF_eq_of_le (h : ℝ → ℂ) {η ξ : ℝ} (hξ : ξ ≤ η) (s : ℝ) : abelF h η ξ s = 0 := by
  have : ξ ∉ Ioo η s := fun hm => absurd hm.1 (not_lt.2 hξ)
  simp [abelF, pairKer2, Set.indicator_of_notMem this]

private theorem integral_abelF_of_lt (h : ℝ → ℂ) {η s : ℝ} (hηs : η < s) :
    ∫ ξ, abelF h η ξ s = (Real.pi : ℂ) * h s := by
  have : (fun ξ => abelF h η ξ s) = fun ξ => h s * ((((Ioo η s).indicator (pairKer η s) ξ : ℝ)) : ℂ) := rfl
  rw [this, integral_const_mul, integral_complex_ofReal, integral_indicator measurableSet_Ioo, pairKer_integral hηs,
    mul_comm]

private theorem integral_norm_abelF_of_lt (h : ℝ → ℂ) {η s : ℝ} (hηs : η < s) :
    ∫ ξ, ‖abelF h η ξ s‖ = ‖h s‖ * Real.pi := by
  have : (fun ξ => ‖abelF h η ξ s‖) = fun ξ => ‖h s‖ * (Ioo η s).indicator (pairKer η s) ξ := by
    funext ξ
    show ‖h s * ((pairKer2 η (ξ, s) : ℝ) : ℂ)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pairKer2_nonneg η (ξ, s))]
    rfl
  rw [this, integral_const_mul, integral_indicator measurableSet_Ioo, pairKer_integral hηs]

private theorem integrable_abelF (h : ℝ → ℂ) (hc : Continuous h) (hs : HasCompactSupport h) (η : ℝ) :
    Integrable (Function.uncurry (abelF h η)) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry (abelF h η)) (volume.prod volume) := by
    have : Function.uncurry (abelF h η) = fun q : ℝ × ℝ => h q.2 * ((pairKer2 η q : ℝ) : ℂ) := by
      funext q
      rfl
    rw [this]
    exact ((hc.measurable.comp measurable_snd).mul
      (Complex.measurable_ofReal.comp (measurable_pairKer2 η))).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  constructor
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have hfun : (fun ξ => Function.uncurry (abelF h η) (ξ, s)) =
        fun ξ => h s * ((((Ioo η s).indicator (pairKer η s) ξ : ℝ)) : ℂ) := rfl
    rw [hfun]
    exact (((integrable_indicator_iff measurableSet_Ioo).2 (pairKer_integrableOn η s)).ofReal).const_mul (h s)
  · have heq : (fun s => ∫ ξ, ‖Function.uncurry (abelF h η) (ξ, s)‖) =
        (Ioi η).indicator (fun s => ‖h s‖ * Real.pi) := by
      funext s
      by_cases hηs : η < s
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hηs)]
        exact integral_norm_abelF_of_lt h hηs
      · rw [Set.indicator_of_notMem (fun hm => hηs (Set.mem_Ioi.1 hm))]
        have : (fun ξ => ‖Function.uncurry (abelF h η) (ξ, s)‖) = fun _ => (0 : ℝ) := by
          funext ξ
          show ‖abelF h η ξ s‖ = 0
          rw [abelF_eq_of_not_lt h hηs ξ, norm_zero]
        rw [this, integral_zero]
    rw [heq]
    refine Integrable.indicator ?_ measurableSet_Ioi
    exact (hc.norm.mul continuous_const).integrable_of_hasCompactSupport ((hs.comp_left norm_zero).mul_right)

private theorem abel_abel (h : ℝ → ℂ) (hc : Continuous h) (hs : HasCompactSupport h) (η : ℝ) :
    ∫ ξ in Ioi η, (∫ s in Ioi ξ, h s / ((Real.sqrt (s - ξ) : ℝ) : ℂ)) / ((Real.sqrt (ξ - η) : ℝ) : ℂ)
      = (Real.pi : ℂ) * ∫ s in Ioi η, h s := by
  have h1 : ∀ ξ ∈ Ioi η,
      (∫ s in Ioi ξ, h s / ((Real.sqrt (s - ξ) : ℝ) : ℂ)) / ((Real.sqrt (ξ - η) : ℝ) : ℂ) = ∫ s, abelF h η ξ s := by
    intro ξ hξ
    have hξ' : η < ξ := Set.mem_Ioi.1 hξ
    rw [← integral_div, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext s
    by_cases hsξ : ξ < s
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hsξ)]
      simp only [abelF, pairKer2, pairKer, Set.indicator_of_mem (Set.mem_Ioo.2 ⟨hξ', hsξ⟩)]
      push_cast
      ring
    · rw [Set.indicator_of_notMem (fun hm => hsξ (Set.mem_Ioi.1 hm))]
      have : ξ ∉ Ioo η s := fun hm => hsξ hm.2
      simp [abelF, pairKer2, Set.indicator_of_notMem this]
  calc ∫ ξ in Ioi η, (∫ s in Ioi ξ, h s / ((Real.sqrt (s - ξ) : ℝ) : ℂ)) / ((Real.sqrt (ξ - η) : ℝ) : ℂ)
      = ∫ ξ in Ioi η, ∫ s, abelF h η ξ s := setIntegral_congr_fun measurableSet_Ioi h1
    _ = ∫ ξ, ∫ s, abelF h η ξ s := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro ξ hξ
        have hξ' : ξ ≤ η := not_lt.1 (fun h' => hξ (Set.mem_Ioi.2 h'))
        simp [abelF_eq_of_le h hξ']
    _ = ∫ s, ∫ ξ, abelF h η ξ s := integral_integral_swap (integrable_abelF h hc hs η)
    _ = ∫ s, (Ioi η).indicator (fun s => (Real.pi : ℂ) * h s) s := by
        congr 1
        funext s
        by_cases hηs : η < s
        · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hηs)]
          exact integral_abelF_of_lt h hηs
        · rw [Set.indicator_of_notMem (fun hm => hηs (Set.mem_Ioi.1 hm))]
          simp [abelF_eq_of_not_lt h hηs]
    _ = (Real.pi : ℂ) * ∫ s in Ioi η, h s := by
        rw [integral_indicator measurableSet_Ioi, integral_const_mul]

private theorem integral_Ioi_deriv_of_hasCompactSupport (g : ℝ → ℂ) (hg : Differentiable ℝ g)
    (hg' : Continuous (deriv g)) (hs : HasCompactSupport g) (η : ℝ) : ∫ s in Ioi η, deriv g s = -g η := by
  have hlim : Filter.Tendsto g Filter.atTop (nhds 0) := by
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall (0 : ℝ)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop R] with s hsR
    by_contra hne
    have hmem : s ∈ tsupport g := subset_tsupport g (by simpa [Function.mem_support] using (Ne.symm hne))
    have := hR hmem
    rw [Real.closedBall_eq_Icc] at this
    linarith [this.2]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => (hg s).hasDerivAt)
    (hg'.integrable_of_hasCompactSupport hs.deriv).integrableOn hlim]
  simp

private noncomputable def abelA (g : ℝ → ℂ) : ℝ → ℂ := convolution abelKer g abelL volume

private theorem abelA_eq (g : ℝ → ℂ) (ξ : ℝ) :
    abelA g ξ = ∫ s in Ioi ξ, g s / ((Real.sqrt (s - ξ) : ℝ) : ℂ) := by
  simp only [abelA, convolution_def, abelL, ContinuousLinearMap.lsmul_apply]
  rw [← integral_sub_left_eq_self (fun t => abelKer t • g (ξ - t)) volume ξ, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext s
  simp only [sub_sub_cancel]
  by_cases hsξ : ξ < s
  · have hneg : ξ - s < 0 := by linarith
    rw [Set.indicator_of_mem (Set.mem_Ioi.2 hsξ), abelKer_of_neg hneg, neg_sub, Complex.real_smul]
    push_cast
    ring
  · have hnn : 0 ≤ ξ - s := by linarith [not_lt.1 hsξ]
    rw [Set.indicator_of_notMem (fun hm => hsξ (Set.mem_Ioi.1 hm)), abelKer_of_nonneg hnn, zero_smul]

private theorem abelA_lin (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g)
    (hgc : HasCompactSupport g) (a b : ℂ) (ξ : ℝ) :
    abelA (fun x => a * f x + b * g x) ξ = a * abelA f ξ + b * abelA g ξ := by
  have h1 := hfc.convolutionExists_right abelL abelKer_locallyIntegrable hf ξ
  have h2 := hgc.convolutionExists_right abelL abelKer_locallyIntegrable hg ξ
  simp only [ConvolutionExistsAt, abelL, ContinuousLinearMap.lsmul_apply] at h1 h2
  simp only [abelA, convolution_def, abelL, ContinuousLinearMap.lsmul_apply]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul a) (h2.const_mul b)]
  congr 1
  funext t
  simp only [Complex.real_smul]
  ring

private noncomputable def abelT (f : ℝ → ℂ) (ξ : ℝ) : ℂ := -(1 / (Real.pi : ℂ)) * abelA (deriv f) ξ

private theorem abelT_lin (f g : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (a b : ℂ) :
    abelT (fun ξ => a * f ξ + b * g ξ) = fun ξ => a * abelT f ξ + b * abelT g ξ := by
  funext ξ
  have hd : deriv (fun x => a * f x + b * g x) = fun x => a * deriv f x + b * deriv g x := by
    funext x
    exact ((((contDiff_infty_iff_deriv.1 hf).1 x).hasDerivAt.const_mul a).add
      (((contDiff_infty_iff_deriv.1 hg).1 x).hasDerivAt.const_mul b)).deriv
  simp only [abelT, hd]
  rw [abelA_lin (deriv f) (deriv g) (contDiff_infty_iff_deriv.1 hf).2.continuous hfc.deriv
    (contDiff_infty_iff_deriv.1 hg).2.continuous hgc.deriv a b ξ]
  ring

private theorem abelT_eq_zero (f : ℝ → ℂ) {R ξ : ℝ} (hf : ∀ x, R ≤ x → f x = 0) (hξ : R ≤ ξ) : abelT f ξ = 0 := by
  rw [abelT, abelA_eq]
  have h0 : ∀ s ∈ Ioi ξ, deriv f s / ((Real.sqrt (s - ξ) : ℝ) : ℂ) = 0 := by
    intro s hs
    have hs' : R < s := lt_of_le_of_lt hξ (Set.mem_Ioi.1 hs)
    have hev : f =ᶠ[nhds s] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hs'] with x hx
      exact hf x (Set.mem_Ioi.1 hx).le
    rw [hev.deriv_eq, deriv_const, zero_div]
  rw [setIntegral_congr_fun measurableSet_Ioi h0, integral_zero, mul_zero]

private theorem abelT_abel (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (η : ℝ) :
    ∫ ξ in Ioi η, abelT f ξ / ((Real.sqrt (ξ - η) : ℝ) : ℂ) = f η := by
  have hd : Continuous (deriv f) := (contDiff_infty_iff_deriv.1 hf).2.continuous
  have hdc : HasCompactSupport (deriv f) := hfc.deriv
  have h1 : ∀ ξ ∈ Ioi η, abelT f ξ / ((Real.sqrt (ξ - η) : ℝ) : ℂ) =
      -(1 / (Real.pi : ℂ)) *
        ((∫ s in Ioi ξ, deriv f s / ((Real.sqrt (s - ξ) : ℝ) : ℂ)) / ((Real.sqrt (ξ - η) : ℝ) : ℂ)) := by
    intro ξ _
    rw [abelT, abelA_eq, mul_div_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul, abel_abel (deriv f) hd hdc η,
    integral_Ioi_deriv_of_hasCompactSupport f (contDiff_infty_iff_deriv.1 hf).1 hd hfc η]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field

private noncomputable def slopeFamily {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (G : ℝ × P → ℂ)
    (p : P) (x : ℝ) : ℂ := fderiv ℝ G (x, p) ((1 : ℝ), (0 : P))

private theorem deriv_slice_eq {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (G : ℝ × P → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (p : P) : deriv (fun ξ => G (ξ, p)) = slopeFamily G p := by
  funext x
  have h1 : HasFDerivAt G (fderiv ℝ G (x, p)) (x, p) := ((contDiff_infty_iff_fderiv.1 hG).1 (x, p)).hasFDerivAt
  have h2 : HasDerivAt (fun ξ : ℝ => (ξ, p)) ((1 : ℝ), (0 : P)) x := (hasDerivAt_id x).prodMk (hasDerivAt_const x p)
  exact (h1.comp_hasDerivAt x h2).deriv

private theorem slice_contDiff {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (G : ℝ × P → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (p : P) : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => G (ξ, p)) :=
  hG.comp (contDiff_prodMk_left p)

private theorem slice_hasCompactSupport {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (G : ℝ × P → ℂ)
    (hGc : HasCompactSupport G) (p : P) : HasCompactSupport (fun ξ => G (ξ, p)) :=
  HasCompactSupport.of_support_subset_isCompact (hGc.image continuous_fst)
    (fun ξ hξ => ⟨(ξ, p), subset_tsupport G (show (ξ, p) ∈ Function.support G from hξ), rfl⟩)

private theorem contDiff_abelT_family {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (G : ℝ × P → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => abelT (fun ξ => G (ξ, q.2)) q.1) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℝ => slopeFamily G q.1 q.2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × P => fderiv ℝ G z ((1 : ℝ), (0 : P))) :=
      (contDiff_infty_iff_fderiv.1 hG).2.clm_apply contDiff_const
    exact h1.comp (contDiff_snd.prodMk contDiff_fst)
  have hk : IsCompact (Prod.fst '' tsupport G) := hGc.image continuous_fst
  have hgs : ∀ (p : P) (x : ℝ), p ∈ (Set.univ : Set P) → x ∉ Prod.fst '' tsupport G → slopeFamily G p x = 0 := by
    intro p x _ hx
    by_contra hne
    apply hx
    refine ⟨(x, p), support_fderiv_subset ℝ ?_, rfl⟩
    rw [Function.mem_support]
    intro h0
    apply hne
    simp [slopeFamily, h0]
  have hconv := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (n := (⊤ : ℕ∞)) abelL isOpen_univ hk hgs
    abelKer_locallyIntegrable (by rw [Set.univ_prod_univ]; exact contDiffOn_univ.2 hsm)
  rw [Set.univ_prod_univ, contDiffOn_univ] at hconv
  have hrw : (fun q : ℝ × P => abelT (fun ξ => G (ξ, q.2)) q.1) =
      fun q : ℝ × P => -(1 / (Real.pi : ℂ)) * convolution abelKer (slopeFamily G q.2) abelL volume q.1 := by
    funext q
    simp only [abelT, abelA, deriv_slice_eq G hG]
  rw [hrw]
  exact contDiff_const.mul (hconv.comp (contDiff_snd.prodMk contDiff_fst))

theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ T : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, T (fun ξ => a * f ξ + b * g ξ) = fun ξ => a * T f ξ + b * T g ξ) ∧
      ∀ G : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => T (fun ξ => G (ξ, q.2)) q.1) ∧
        (∀ R : ℝ, (∀ (p : P) (ξ : ℝ), R ≤ ξ → G (ξ, p) = 0) →
          ∀ (p : P) (ξ : ℝ), R ≤ ξ → T (fun ξ' => G (ξ', p)) ξ = 0) ∧
        ∀ (η : ℝ) (p : P),
          ∫ ξ in Set.Ioi η, T (fun ξ' => G (ξ', p)) ξ / ((Real.sqrt (ξ - η) : ℝ) : ℂ) = G (η, p) := by
  refine ⟨abelT, fun f g hf hfc hg hgc a b => abelT_lin f g hf hfc hg hgc a b, fun G hG hGc => ?_⟩
  refine ⟨contDiff_abelT_family G hG hGc,
    fun R hR p ξ hξ => abelT_eq_zero (fun ξ' => G (ξ', p)) (fun x hx => hR p x hx) hξ, fun η p => ?_⟩
  exact abelT_abel (fun ξ' => G (ξ', p)) (slice_contDiff G hG p) (slice_hasCompactSupport G hGc p) η

end S_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq
end P2MW
export P2MW.S_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq (solution)
