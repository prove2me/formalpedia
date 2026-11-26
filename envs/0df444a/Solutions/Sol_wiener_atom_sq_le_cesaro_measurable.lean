-- Prove2me | solution 1 for wiener_atom_sq_le_cesaro_measurable
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:26:22.540816+00:00
-- url     : https://prove2.me/submissions/2de4e9f2-7c34-4a36-a220-799cc982af00

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open scoped Topology
set_option autoImplicit false

lemma abs_cos_le_one' (t : ℝ) : |Real.cos t| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩

lemma abs_sin_le_one' (t : ℝ) : |Real.sin t| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩

/-- Continuity of a parametric integral of a bounded continuous function. -/
lemma cont_param {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hφb : ∀ t, |φ t| ≤ 1)
    (g : α → ℝ) (hg : Measurable g) :
    Continuous fun u : ℝ => ∫ a, φ (u * g a) ∂μ := by
  refine SeqContinuous.continuous ?_
  intro s u hs
  simp only [Function.comp_apply]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
    (integrable_const 1) ?_ ?_
  · intro n
    exact (hφ.measurable.comp (measurable_const.mul hg)).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]; exact hφb _
  · exact Filter.Eventually.of_forall fun a => by
      have h1 : Tendsto (fun n => s n * g a) atTop (𝓝 (u * g a)) := hs.mul tendsto_const_nhds
      exact (hφ.tendsto _).comp h1

/-- The Fejér–Wiener kernel: `cesaroKer U w = ∫ u in [0,U], cos (w * u) du`. -/
noncomputable def cesaroKer (U w : ℝ) : ℝ := ∫ u in Set.Icc 0 U, Real.cos (w * u) ∂volume

lemma cesaroKer_zero {U : ℝ} (hU : 0 ≤ U) : cesaroKer U 0 = U := by
  show ∫ u in Set.Icc (0 : ℝ) U, Real.cos (0 * u) ∂volume = U
  simp only [zero_mul, Real.cos_zero]
  rw [setIntegral_const]
  have hreal : volume.real (Set.Icc (0 : ℝ) U) = U := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ U - 0),
      sub_zero]
  rw [hreal]
  simp

lemma cesaroKer_eq {U : ℝ} (hU : 0 ≤ U) (w : ℝ) :
    cesaroKer U w = if w = 0 then U else Real.sin (w * U) / w := by
  by_cases hw : w = 0
  · subst hw
    rw [if_pos rfl]
    exact cesaroKer_zero hU
  · rw [if_neg hw]
    show ∫ u in Set.Icc (0 : ℝ) U, Real.cos (w * u) ∂volume = Real.sin (w * U) / w
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hU,
      intervalIntegral.integral_comp_mul_left (f := Real.cos) hw, integral_cos]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma cesaroKer_abs_le {U : ℝ} (hU : 0 ≤ U) (w : ℝ) : |cesaroKer U w| ≤ U := by
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' (μ := volume)
    (s := Set.Icc (0 : ℝ) U) (f := fun u => Real.cos (w * u)) (C := 1)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (Filter.Eventually.of_forall fun u _ => by
      rw [Real.norm_eq_abs]; exact abs_cos_le_one' _)
  have hreal : volume.real (Set.Icc (0 : ℝ) U) = U := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ U - 0),
      sub_zero]
  rw [hreal, one_mul, Real.norm_eq_abs] at h
  exact h

lemma cesaroKer_cont (U : ℝ) : Continuous (cesaroKer U) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) U)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have h := cont_param (volume.restrict (Set.Icc (0 : ℝ) U)) Real.cos Real.continuous_cos
    abs_cos_le_one' (fun u : ℝ => u) measurable_id
  exact h

/-- The key identity: `|φ(u)|²` as a double integral of `cos (u * (Z ω - Z ω'))`. -/
lemma key_id {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (u : ℝ) :
    (∫ ω, Real.cos (u * Z ω) ∂P) ^ 2 + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2
      = ∫ p : Ω × Ω, Real.cos (u * (Z p.1 - Z p.2)) ∂(P.prod P) := by
  have hc : Integrable (fun p : Ω × Ω => Real.cos (u * Z p.1) * Real.cos (u * Z p.2))
      (P.prod P) := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun p => ?_)
    · exact ((Real.continuous_cos.measurable.comp
        (measurable_const.mul (hZ.comp measurable_fst))).mul
        (Real.continuous_cos.measurable.comp
          (measurable_const.mul (hZ.comp measurable_snd)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (abs_cos_le_one' _) (abs_cos_le_one' _) (abs_nonneg _) zero_le_one).trans
        (by norm_num)
  have hs : Integrable (fun p : Ω × Ω => Real.sin (u * Z p.1) * Real.sin (u * Z p.2))
      (P.prod P) := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun p => ?_)
    · exact ((Real.continuous_sin.measurable.comp
        (measurable_const.mul (hZ.comp measurable_fst))).mul
        (Real.continuous_sin.measurable.comp
          (measurable_const.mul (hZ.comp measurable_snd)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (abs_sin_le_one' _) (abs_sin_le_one' _) (abs_nonneg _) zero_le_one).trans
        (by norm_num)
  have e1 : (∫ ω, Real.cos (u * Z ω) ∂P) * (∫ ω, Real.cos (u * Z ω) ∂P)
      = ∫ p : Ω × Ω, Real.cos (u * Z p.1) * Real.cos (u * Z p.2) ∂(P.prod P) :=
    (integral_prod_mul _ _).symm
  have e2 : (∫ ω, Real.sin (u * Z ω) ∂P) * (∫ ω, Real.sin (u * Z ω) ∂P)
      = ∫ p : Ω × Ω, Real.sin (u * Z p.1) * Real.sin (u * Z p.2) ∂(P.prod P) :=
    (integral_prod_mul _ _).symm
  calc (∫ ω, Real.cos (u * Z ω) ∂P) ^ 2 + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2
      = (∫ ω, Real.cos (u * Z ω) ∂P) * (∫ ω, Real.cos (u * Z ω) ∂P)
        + (∫ ω, Real.sin (u * Z ω) ∂P) * (∫ ω, Real.sin (u * Z ω) ∂P) := by
        rw [pow_two, pow_two]
    _ = (∫ p : Ω × Ω, Real.cos (u * Z p.1) * Real.cos (u * Z p.2) ∂(P.prod P))
        + (∫ p : Ω × Ω, Real.sin (u * Z p.1) * Real.sin (u * Z p.2) ∂(P.prod P)) := by
        rw [e1, e2]
    _ = ∫ p : Ω × Ω, (Real.cos (u * Z p.1) * Real.cos (u * Z p.2)
        + Real.sin (u * Z p.1) * Real.sin (u * Z p.2)) ∂(P.prod P) :=
        (integral_add hc hs).symm
    _ = ∫ p : Ω × Ω, Real.cos (u * (Z p.1 - Z p.2)) ∂(P.prod P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          show Real.cos (u * Z p.1) * Real.cos (u * Z p.2)
              + Real.sin (u * Z p.1) * Real.sin (u * Z p.2) = Real.cos (u * (Z p.1 - Z p.2))
          rw [← Real.cos_sub]; congr 1; ring

/-- The Cesàro average of `|φ|²` equals the averaged kernel integral over the product space. -/
lemma avg_eq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (U : ℝ) :
    (∫ p : Ω × Ω, cesaroKer U (Z p.1 - Z p.2) / U ∂(P.prod P))
      = (∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
          + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) U)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hw : Measurable fun p : Ω × Ω => Z p.1 - Z p.2 :=
    (hZ.comp measurable_fst).sub (hZ.comp measurable_snd)
  have hInt : Integrable (Function.uncurry fun (p : Ω × Ω) (u : ℝ) =>
        Real.cos ((Z p.1 - Z p.2) * u))
      ((P.prod P).prod (volume.restrict (Set.Icc 0 U))) := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun q => ?_)
    · exact (Real.continuous_cos.measurable.comp
        ((hw.comp measurable_fst).mul measurable_snd)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact abs_cos_le_one' _
  calc (∫ p : Ω × Ω, cesaroKer U (Z p.1 - Z p.2) / U ∂(P.prod P))
      = (∫ p : Ω × Ω, cesaroKer U (Z p.1 - Z p.2) ∂(P.prod P)) / U := by
        rw [show (fun p : Ω × Ω => cesaroKer U (Z p.1 - Z p.2) / U)
            = (fun p : Ω × Ω => U⁻¹ * cesaroKer U (Z p.1 - Z p.2)) from
          funext fun p => by rw [div_eq_mul_inv, mul_comm]]
        rw [integral_const_mul, div_eq_mul_inv, mul_comm]
    _ = (∫ p : Ω × Ω, ∫ u in Set.Icc 0 U, Real.cos ((Z p.1 - Z p.2) * u) ∂volume
          ∂(P.prod P)) / U := by
        congr 1
    _ = (∫ u in Set.Icc 0 U, ∫ p : Ω × Ω, Real.cos ((Z p.1 - Z p.2) * u) ∂(P.prod P)
          ∂volume) / U := by
        congr 1
        exact integral_integral_swap hInt
    _ = (∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
          + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U := by
        congr 1
        have hstep : ∀ u : ℝ, (∫ p : Ω × Ω, Real.cos ((Z p.1 - Z p.2) * u) ∂(P.prod P))
            = (∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
              + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2 := by
          intro u
          have hcomm : (∫ p : Ω × Ω, Real.cos ((Z p.1 - Z p.2) * u) ∂(P.prod P))
              = ∫ p : Ω × Ω, Real.cos (u * (Z p.1 - Z p.2)) ∂(P.prod P) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun p => by
              show Real.cos ((Z p.1 - Z p.2) * u) = Real.cos (u * (Z p.1 - Z p.2))
              rw [mul_comm]
          rw [hcomm, key_id P Z hZ u]
        exact integral_congr_ae (Filter.Eventually.of_forall hstep)

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Omega → Real) (hZ : Measurable Z) :
  ∀ x : Real, ∀ ε : ENNReal, 0 < ε →
    ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
      (P {omega : Omega | Z omega = x})^2 ≤
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫ omega, Real.cos (u * Z omega) ∂P)^2 + (∫ omega, Real.sin (u * Z omega) ∂P)^2) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε := by
  intro x ε hε
  have h1 : ∀ s : Set Omega, P s ≤ 1 := by
    intro s
    have h : P s ≤ P Set.univ := measure_mono (Set.subset_univ s)
    rwa [measure_univ] at h
  have hν1 : ∀ s : Set (Omega × Omega), (P.prod P) s ≤ 1 := by
    intro s
    have h : (P.prod P) s ≤ (P.prod P) Set.univ := measure_mono (Set.subset_univ s)
    rwa [measure_univ] at h
  by_cases hεtop : ε = ⊤
  · refine ⟨0, fun U _ => ?_⟩
    rw [hεtop]
    exact le_top.trans le_add_self
  · have hεtoReal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hw : Measurable fun p : Omega × Omega => Z p.1 - Z p.2 :=
      (hZ.comp measurable_fst).sub (hZ.comp measurable_snd)
    have hD : MeasurableSet {p : Omega × Omega | Z p.1 = Z p.2} :=
      measurableSet_eq_fun (hZ.comp measurable_fst) (hZ.comp measurable_snd)
    -- Dominated convergence: the averaged kernel tends to the diagonal mass.
    have hlim : Tendsto (fun U => ∫ p : Omega × Omega, cesaroKer U (Z p.1 - Z p.2) / U
          ∂(P.prod P))
        atTop (𝓝 ((P.prod P) {p : Omega × Omega | Z p.1 = Z p.2}).toReal) := by
      have hInt : (∫ p : Omega × Omega, (if Z p.1 = Z p.2 then (1 : ℝ) else 0) ∂(P.prod P))
          = ((P.prod P) {p : Omega × Omega | Z p.1 = Z p.2}).toReal := by
        have hfun : (fun p : Omega × Omega => if Z p.1 = Z p.2 then (1 : ℝ) else 0)
            = {p : Omega × Omega | Z p.1 = Z p.2}.indicator (fun _ => (1 : ℝ)) := by
          funext p
          by_cases hp : Z p.1 = Z p.2
          · rw [if_pos hp,
              Set.indicator_of_mem (show p ∈ {p : Omega × Omega | Z p.1 = Z p.2} from hp)]
          · rw [if_neg hp,
              Set.indicator_of_notMem (show p ∉ {p : Omega × Omega | Z p.1 = Z p.2} from hp)]
        rw [hfun, integral_indicator_const 1 hD, measureReal_def, smul_eq_mul, mul_one]
      have hDCT : Tendsto (fun U => ∫ p : Omega × Omega, cesaroKer U (Z p.1 - Z p.2) / U
            ∂(P.prod P))
          atTop (𝓝 (∫ p : Omega × Omega, (if Z p.1 = Z p.2 then (1 : ℝ) else 0)
            ∂(P.prod P))) := by
        refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (fun _ => (1 : ℝ)) ?_ ?_ (integrable_const 1) ?_
        · exact Filter.Eventually.of_forall fun U =>
            (((cesaroKer_cont U).measurable.comp hw).div_const U).aestronglyMeasurable
        · refine Filter.eventually_atTop.mpr ⟨1, fun U hU =>
            Filter.Eventually.of_forall fun p => ?_⟩
          have hU0 : (0 : ℝ) ≤ U := le_trans zero_le_one hU
          have hUpos : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hUpos, div_le_one hUpos]
          exact cesaroKer_abs_le hU0 _
        · refine Filter.Eventually.of_forall fun p => ?_
          by_cases hp : Z p.1 = Z p.2
          · rw [if_pos hp]
            have hwp : Z p.1 - Z p.2 = 0 := sub_eq_zero.mpr hp
            rw [hwp]
            refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
            refine Filter.eventually_atTop.mpr ⟨1, fun U hU => ?_⟩
            show (1 : ℝ) = cesaroKer U 0 / U
            rw [cesaroKer_zero (le_trans zero_le_one hU),
              div_self (ne_of_gt (lt_of_lt_of_le one_pos hU))]
          · rw [if_neg hp]
            have hwp : Z p.1 - Z p.2 ≠ 0 := sub_ne_zero.mpr hp
            refine squeeze_zero_norm' (a := fun U : ℝ => |Z p.1 - Z p.2|⁻¹ / U) ?_ ?_
            · refine Filter.eventually_atTop.mpr ⟨1, fun U hU => ?_⟩
              have hU0 : (0 : ℝ) ≤ U := le_trans zero_le_one hU
              have hUpos : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU
              have hker : |cesaroKer U (Z p.1 - Z p.2)| ≤ |Z p.1 - Z p.2|⁻¹ := by
                rw [cesaroKer_eq hU0 (Z p.1 - Z p.2), if_neg hwp, abs_div,
                  div_le_iff₀ (abs_pos.mpr hwp), inv_mul_cancel₀ (abs_ne_zero.mpr hwp)]
                exact abs_sin_le_one' _
              rw [Real.norm_eq_abs, abs_div, abs_of_pos hUpos]
              simp only [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hker (inv_nonneg.mpr hUpos.le)
            · have hlim0 : Tendsto (fun U : ℝ => |Z p.1 - Z p.2|⁻¹ * U⁻¹) atTop
                  (𝓝 (|Z p.1 - Z p.2|⁻¹ * 0)) :=
                tendsto_const_nhds.mul tendsto_inv_atTop_zero
              simpa [div_eq_mul_inv] using hlim0
      rwa [hInt] at hDCT
    have hAvg : Tendsto (fun U => (∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
            + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U) atTop
        (𝓝 ((P.prod P) {p : Omega × Omega | Z p.1 = Z p.2}).toReal) :=
      Filter.Tendsto.congr (fun U => avg_eq P Z hZ U) hlim
    obtain ⟨U0, hU0⟩ := (Metric.tendsto_atTop.mp hAvg) (ε.toReal / 2) (half_pos hεtoReal)
    refine ⟨max U0 1, fun U hU => ?_⟩
    have hU1 : (1 : ℝ) ≤ U := le_trans (le_max_right U0 1) hU
    have hUU0 : U0 ≤ U := le_trans (le_max_left U0 1) hU
    have hUpos : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU1
    have hdist : dist ((∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
            + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U)
        ((P.prod P) {p : Omega × Omega | Z p.1 = Z p.2}).toReal < ε.toReal / 2 :=
      hU0 U hUU0
    rw [Real.dist_eq] at hdist
    have hfin1 : (P {omega : Omega | Z omega = x}) ^ 2 ≠ ⊤ := by
      rw [pow_two]
      exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (by simp) (h1 _))
        (ne_top_of_le_ne_top (by simp) (h1 _))
    have hfin2 : (P.prod P) {p : Omega × Omega | Z p.1 = Z p.2} ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (hν1 _)
    have hL : (P {omega : Omega | Z omega = x}).toReal ^ 2
        ≤ ((P.prod P) {p : Omega × Omega | Z p.1 = Z p.2}).toReal := by
      have hsub : {omega : Omega | Z omega = x} ×ˢ {omega : Omega | Z omega = x}
          ⊆ {p : Omega × Omega | Z p.1 = Z p.2} := by
        rintro p ⟨hp1, hp2⟩
        exact hp1.trans hp2.symm
      have hle : (P {omega : Omega | Z omega = x}) ^ 2
          ≤ (P.prod P) {p : Omega × Omega | Z p.1 = Z p.2} := by
        calc (P {omega : Omega | Z omega = x}) ^ 2
            = P {omega : Omega | Z omega = x} * P {omega : Omega | Z omega = x} := pow_two _
          _ = (P.prod P) ({omega : Omega | Z omega = x} ×ˢ {omega : Omega | Z omega = x}) :=
              (MeasureTheory.Measure.prod_prod _ _).symm
          _ ≤ (P.prod P) {p : Omega × Omega | Z p.1 = Z p.2} := measure_mono hsub
      have htoReal := (ENNReal.toReal_le_toReal hfin1 hfin2).mpr hle
      rwa [ENNReal.toReal_pow] at htoReal
    have hFint_nn : ∀ u : ℝ, 0 ≤ (∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
        + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2 := fun u => by positivity
    have hFint_int : IntegrableOn (fun u => (∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
        + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) (Set.Icc 0 U) volume := by
      have hc : Continuous fun u => ∫ ω, Real.cos (u * Z ω) ∂P :=
        cont_param P Real.cos Real.continuous_cos abs_cos_le_one' Z hZ
      have hs : Continuous fun u => ∫ ω, Real.sin (u * Z ω) ∂P :=
        cont_param P Real.sin Real.continuous_sin abs_sin_le_one' Z hZ
      exact ((hc.pow 2).add (hs.pow 2)).integrableOn_Icc
    have hgoal : (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫ omega, Real.cos (u * Z omega) ∂P)^2 + (∫ omega, Real.sin (u * Z omega) ∂P)^2) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε
        = ENNReal.ofReal ((∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
            + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U) + ε := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (integral_nonneg hFint_nn),
        ENNReal.ofReal_inv_of_pos hUpos,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFint_int
          (Filter.Eventually.of_forall hFint_nn)]
    rw [hgoal]
    have hstep1 : (P {omega : Omega | Z omega = x}) ^ 2
        = ENNReal.ofReal ((P {omega : Omega | Z omega = x}).toReal ^ 2) := by
      rw [← ENNReal.toReal_pow, ENNReal.ofReal_toReal hfin1]
    rw [hstep1]
    have havgL : ((P.prod P) {p : Omega × Omega | Z p.1 = Z p.2}).toReal
        ≤ (∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
            + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U + ε.toReal := by
      have h := (abs_lt.mp hdist).1
      linarith [h, hεtoReal]
    have havg_nonneg : 0 ≤ (∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
          + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U :=
      div_nonneg (integral_nonneg hFint_nn) hUpos.le
    refine le_trans (ENNReal.ofReal_le_ofReal hL) ?_
    calc ENNReal.ofReal ((P.prod P) {p : Omega × Omega | Z p.1 = Z p.2}).toReal
        ≤ ENNReal.ofReal ((∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
            + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U + ε.toReal) :=
          ENNReal.ofReal_le_ofReal havgL
      _ = ENNReal.ofReal ((∫ u in Set.Icc 0 U, ((∫ ω, Real.cos (u * Z ω) ∂P) ^ 2
            + (∫ ω, Real.sin (u * Z ω) ∂P) ^ 2) ∂volume) / U) + ε := by
          rw [ENNReal.ofReal_add havg_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hεtop]
