-- Prove2me | solution 1 for levy_foundations_levyLocalCharExponent_eq_charExponent
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:34.577581+00:00
-- url     : https://prove2.me/submissions/3e817bcc-f356-433a-b4b3-f40ae46854f9

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Definitions.Def_levy_foundations_levyExpFormula

open MeasureTheory Filter Topology
open scoped NNReal


namespace Lv2Aux

lemma map_sub_stationary {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : LevyFoundations.IsLevyProcess X μ) (s u : ℝ≥0) :
    μ.map (fun ω => X (s + u) ω - X s ω) = μ.map (X u) := by
  have := (h.stationary_increments s u).map_eq
  have h0 := h.start_zero
  have e : LevyFoundations.increment X 0 u = X u := by
    funext ω; simp [LevyFoundations.increment, h0]
  have e' : LevyFoundations.increment X s (s + u) = fun ω => X (s + u) ω - X s ω := rfl
  rwa [e, e'] at this

lemma charFun_add {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (s u : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + u))) ξ = charFun (μ.map (X s)) ξ * charFun (μ.map (X u)) ξ := by
  have hind := h.indep_increments.indepFun_sub_sub (r := 0) (s := s) (t := s + u)
    zero_le le_self_add
  have h0 := h.start_zero
  have e1 : (X s - X 0) = X s := by funext ω; simp [h0]
  rw [e1] at hind
  have e2 : (X s + (X (s + u) - X s)) = X (s + u) := by funext ω; simp
  have := ProbabilityTheory.IndepFun.charFun_map_add_eq_mul (hX s).aemeasurable
    (((hX (s + u)).sub (hX s)).aemeasurable) hind
  rw [e2] at this
  rw [congrFun this ξ, Pi.mul_apply]
  congr 2
  exact map_sub_stationary h s u


lemma charFun_zero_time {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ) (ξ : E) :
    charFun (μ.map (X 0)) ξ = 1 := by
  have h0 := h.start_zero
  simp [h0, Measure.map_const, charFun_apply]

lemma tendsto_charFun_zero {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (ξ : E) :
    Tendsto (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) (𝓝 0) (𝓝 1) := by
  have hrep : ∀ t : ℝ≥0, charFun (μ.map (X t)) ξ =
      ∫ ω, Complex.exp ((inner ℝ (X t ω) ξ : ℝ) * Complex.I) ∂μ := by
    intro t
    rw [charFun_apply, integral_map (hX t).aemeasurable (by fun_prop)]
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 (0 : ℝ≥0))
    (F := fun (t : ℝ≥0) ω => Complex.exp ((inner ℝ (X t ω) ξ : ℝ) * Complex.I))
    (f := fun ω => Complex.exp ((inner ℝ (X 0 ω) ξ : ℝ) * Complex.I)) (fun _ => 1)
    (Filter.Eventually.of_forall fun t => by
      exact (by have := hX t; fun_prop : Measurable fun ω => Complex.exp ((inner ℝ (X t ω) ξ : ℝ) * Complex.I)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun ω => by
      simp [Complex.norm_exp_ofReal_mul_I])
    (integrable_const _) ?_
  · have h1 : charFun (μ.map (X 0)) ξ = 1 := charFun_zero_time h ξ
    have h2 : (∫ ω, Complex.exp ((inner ℝ (X 0 ω) ξ : ℝ) * Complex.I) ∂μ) = 1 := by
      rw [← hrep 0, h1]
    rw [h2] at hlim
    simpa only [hrep] using hlim
  · filter_upwards [h.cadlag_ae] with ω hω
    have h0 := hω 0
    have hc : ContinuousAt (fun t : ℝ≥0 => X t ω) 0 := by
      have := h0.1
      have hI : Set.Ici (0 : ℝ≥0) = Set.univ := by ext x; simp
      rwa [hI, continuousWithinAt_univ] at this
    exact ((by fun_prop : Continuous fun x : E => Complex.exp ((inner ℝ x ξ : ℝ) * Complex.I)).continuousAt.comp hc).tendsto



lemma cont_charFun {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t))
    (ξ : E) :
    Continuous (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) := by
  set φ : ℝ≥0 → ℂ := fun t => charFun (μ.map (X t)) ξ with hφ
  have hφ0 : φ 0 = 1 := charFun_zero_time h ξ
  have hφadd : ∀ s u, φ (s + u) = φ s * φ u := fun s u => charFun_add h hX s u ξ
  have hφle : ∀ t, ‖φ t‖ ≤ 1 := by
    intro t
    have : IsProbabilityMeasure (μ.map (X t)) := Measure.isProbabilityMeasure_map (hX t).aemeasurable
    exact norm_charFun_le_one ξ
  have hφtend : Tendsto φ (𝓝 0) (𝓝 1) := tendsto_charFun_zero h hX ξ
  have hsub : ∀ t0 : ℝ≥0, Tendsto (fun s : ℝ≥0 => ‖φ (s - t0) - 1‖ + ‖φ (t0 - s) - 1‖)
      (𝓝 t0) (𝓝 0) := by
    intro t0
    have h1 : Tendsto (fun s : ℝ≥0 => s - t0) (𝓝 t0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ≥0 => s - t0) := continuous_id.sub continuous_const
      simpa using hc.tendsto t0
    have h2 : Tendsto (fun s : ℝ≥0 => t0 - s) (𝓝 t0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ≥0 => t0 - s) := continuous_const.sub continuous_id
      simpa using hc.tendsto t0
    have h3 : ∀ {g : ℝ≥0 → ℝ≥0}, Tendsto g (𝓝 t0) (𝓝 0) →
        Tendsto (fun s => ‖φ (g s) - 1‖) (𝓝 t0) (𝓝 0) := by
      intro g hg
      have := ((hφtend.comp hg).sub_const 1).norm
      simpa using this
    simpa using (h3 h1).add (h3 h2)
  refine continuous_iff_continuousAt.2 fun t0 => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) (hsub t0)
  rcases le_total t0 s with hs | hs
  · have e : φ s = φ t0 * φ (s - t0) := by
      rw [← hφadd, add_tsub_cancel_of_le hs]
    have e2 : t0 - s = 0 := tsub_eq_zero_of_le hs
    rw [e2, hφ0, sub_self, norm_zero, add_zero]
    calc ‖φ s - φ t0‖ = ‖φ t0‖ * ‖φ (s - t0) - 1‖ := by
          rw [← norm_mul]; congr 1; rw [e]; ring
      _ ≤ 1 * ‖φ (s - t0) - 1‖ := mul_le_mul_of_nonneg_right (hφle t0) (norm_nonneg _)
      _ = _ := one_mul _
  · have e : φ t0 = φ s * φ (t0 - s) := by
      rw [← hφadd, add_tsub_cancel_of_le hs]
    have e2 : s - t0 = 0 := tsub_eq_zero_of_le hs
    rw [e2, hφ0, sub_self, norm_zero, zero_add]
    calc ‖φ s - φ t0‖ = ‖φ t0 - φ s‖ := norm_sub_rev _ _
      _ = ‖φ s‖ * ‖φ (t0 - s) - 1‖ := by
          rw [← norm_mul]; congr 1; rw [e]; ring
      _ ≤ 1 * ‖φ (t0 - s) - 1‖ := mul_le_mul_of_nonneg_right (hφle s) (norm_nonneg _)
      _ = _ := one_mul _


lemma exp_of_mult (φ : ℝ≥0 → ℂ) (hcont : Continuous φ)
    (hadd : ∀ s u, φ (s + u) = φ s * φ u) (h0 : φ 0 = 1) :
    ∃ (a : ℂ) (δ : ℝ≥0), 0 < δ ∧ (∀ t : ℝ≥0, φ t = Complex.exp (((t : ℝ) : ℂ) * a)) ∧
      ∀ s : ℝ≥0, 0 < s → s ≤ δ → Complex.log (φ s) = ((s : ℝ) : ℂ) * a := by
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.continuous_iff.1 hcont 0 (1 / 2) (by norm_num)
  set δ : ℝ≥0 := ⟨δ0 / 2, by linarith⟩ with hδdef
  have hδpos : 0 < δ := by
    show (0 : ℝ≥0) < ⟨δ0 / 2, _⟩
    exact_mod_cast (by linarith : (0:ℝ) < δ0 / 2)
  have hδreal : (δ : ℝ) = δ0 / 2 := rfl
  have H : ∀ u : ℝ≥0, u ≤ δ → ‖φ u - 1‖ < 1 / 2 := by
    intro u hu
    have h1 : dist u 0 < δ0 := by
      have e : dist u 0 = (u : ℝ) := by
        rw [NNReal.dist_eq]; simp
      have : (u : ℝ) ≤ δ0 / 2 := by rw [← hδreal]; exact_mod_cast hu
      rw [e]
      linarith
    have := hδ0' u h1
    rwa [h0, dist_eq_norm] at this
  have hre : ∀ u : ℝ≥0, u ≤ δ → 0 < (φ u).re := by
    intro u hu
    have h1 := H u hu
    have h2 : |(φ u - 1).re| ≤ ‖φ u - 1‖ := Complex.abs_re_le_norm _
    have h3 : (φ u - 1).re = (φ u).re - 1 := by simp
    rw [h3] at h2
    have := (abs_le.1 h2).1
    linarith
  have hne : ∀ u : ℝ≥0, u ≤ δ → φ u ≠ 0 := by
    intro u hu h
    have := hre u hu
    rw [h] at this
    simp at this
  have harg : ∀ u : ℝ≥0, u ≤ δ → |Complex.arg (φ u)| < Real.pi / 2 := fun u hu =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre u hu))
  have hLadd : ∀ u v : ℝ≥0, u + v ≤ δ →
      Complex.log (φ (u + v)) = Complex.log (φ u) + Complex.log (φ v) := by
    intro u v huv
    have hu : u ≤ δ := le_trans le_self_add huv
    have hv : v ≤ δ := le_trans le_add_self huv
    rw [hadd]
    refine (Complex.log_mul_eq_add_log_iff (hne u hu) (hne v hv)).2 ?_
    have h1 := abs_lt.1 (harg u hu)
    have h2 := abs_lt.1 (harg v hv)
    constructor <;> linarith [Real.pi_pos]
  have hLcont : ∀ u : ℝ≥0, u ≤ δ → ContinuousAt (fun u => Complex.log (φ u)) u := by
    intro u hu
    exact hcont.continuousAt.clog (Complex.mem_slitPlane_iff.2 (Or.inl (hre u hu)))
  have hmul : ∀ N : ℕ, ∀ u : ℝ≥0, (N : ℝ≥0) * u ≤ δ →
      Complex.log (φ (N * u)) = N * Complex.log (φ u) := by
    intro N
    induction N with
    | zero => intro u _; simp [h0]
    | succ N ih =>
      intro u hu
      have e : ((N + 1 : ℕ) : ℝ≥0) * u = N * u + u := by push_cast; ring
      rw [e] at hu ⊢
      rw [hLadd _ _ hu, ih u (le_trans le_self_add hu)]
      push_cast
      ring
  have hkN : ∀ N k : ℕ, 0 < N → k ≤ N →
      Complex.log (φ (k * (δ / N))) = (k : ℂ) / N * Complex.log (φ δ) := by
    intro N k hN hk
    have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
    have hNd : (N : ℝ≥0) * (δ / N) = δ := mul_div_cancel₀ _ hN0
    have h1 := hmul N (δ / N) (by rw [hNd])
    rw [hNd] at h1
    have h2 := hmul k (δ / N) (by
      calc (k : ℝ≥0) * (δ / N) ≤ N * (δ / N) := mul_le_mul_left (by exact_mod_cast hk) _
        _ = δ := hNd)
    rw [h2]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [h1]
    field_simp
  have hlin : ∀ u : ℝ≥0, u ≤ δ →
      Complex.log (φ u) = (((u : ℝ) / δ : ℝ) : ℂ) * Complex.log (φ δ) := by
    intro u hu
    set x : ℝ := (u : ℝ) / δ with hx
    have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδpos
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := by
      rw [hx, div_le_one hδ0']; exact_mod_cast hu
    set kN : ℕ → ℕ := fun N => ⌊x * N⌋₊ with hkNdef
    have hk_le : ∀ N, kN N ≤ N := by
      intro N
      have h1 : (kN N : ℝ) ≤ x * N := Nat.floor_le (by positivity)
      have h2 : x * N ≤ N := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
      exact_mod_cast h1.trans h2
    set un : ℕ → ℝ≥0 := fun N => (kN N : ℝ≥0) * (δ / N) with hun
    have hun_real : ∀ N : ℕ, (un N : ℝ) = ((kN N : ℝ) / N) * δ := by
      intro N
      simp only [hun]
      push_cast
      ring
    have hfl : Filter.Tendsto (fun N : ℕ => (kN N : ℝ) / N) Filter.atTop (nhds x) :=
      (tendsto_nat_floor_mul_div_atTop hx0).comp tendsto_natCast_atTop_atTop
    have hun_t : Filter.Tendsto un Filter.atTop (nhds u) := by
      rw [← NNReal.tendsto_coe]
      have : Filter.Tendsto (fun N : ℕ => ((kN N : ℝ) / N) * δ) Filter.atTop (nhds (x * δ)) :=
        hfl.mul_const _
      have hxδ : x * δ = u := by rw [hx]; field_simp
      rw [hxδ] at this
      exact this.congr (fun N => (hun_real N).symm)
    have hL1 : Filter.Tendsto (fun N => Complex.log (φ (un N))) Filter.atTop
        (nhds (Complex.log (φ u))) := (hLcont u hu).tendsto.comp hun_t
    have hL2 : Filter.Tendsto (fun N : ℕ => ((((kN N : ℝ) / N : ℝ)) : ℂ) * Complex.log (φ δ))
        Filter.atTop (nhds ((x : ℂ) * Complex.log (φ δ))) :=
      ((Complex.continuous_ofReal.tendsto _).comp hfl).mul_const _
    refine tendsto_nhds_unique hL1 (hL2.congr' ?_)
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    simp only [hun]
    rw [hkN N (kN N) hN (hk_le N)]
    push_cast
    ring
  set a : ℂ := Complex.log (φ δ) / ((δ : ℝ) : ℂ) with ha
  have hδc : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδpos.ne'
  have hLa : ∀ u : ℝ≥0, u ≤ δ → Complex.log (φ u) = ((u : ℝ) : ℂ) * a := by
    intro u hu
    rw [hlin u hu, ha]
    push_cast
    field_simp
  have hexp_small : ∀ u : ℝ≥0, u ≤ δ → φ u = Complex.exp (((u : ℝ) : ℂ) * a) := by
    intro u hu
    rw [← hLa u hu, Complex.exp_log (hne u hu)]
  have hpow : ∀ (N : ℕ) (u : ℝ≥0), φ (N * u) = φ u ^ N := by
    intro N
    induction N with
    | zero => intro u; simp [h0]
    | succ N ih =>
      intro u
      have e : ((N + 1 : ℕ) : ℝ≥0) * u = N * u + u := by push_cast; ring
      rw [e, hadd, ih, pow_succ]
  refine ⟨a, δ, hδpos, ?_, fun s _ hs => hLa s hs⟩
  intro t
  obtain ⟨N, hN⟩ := exists_nat_ge ((t : ℝ) / δ)
  have hN' : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  set M : ℕ := N + 1 with hM
  have hM0 : (M : ℝ≥0) ≠ 0 := by positivity
  have hu : t / M ≤ δ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [div_le_iff₀ hN']
    have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδpos
    rw [div_le_iff₀ hδ0'] at hN
    rw [hM]; push_cast
    nlinarith
  have e : t = M * (t / M) := (mul_div_cancel₀ _ hM0).symm
  have h1 : φ t = φ (t / M) ^ M := by
    conv_lhs => rw [e]
    exact hpow M _
  rw [h1, hexp_small _ hu, ← Complex.exp_nat_mul]
  congr 1
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  push_cast
  field_simp



lemma cadlag_local_bound {E : Type*} [NormedAddCommGroup E] (f : ℝ≥0 → E)
    (hf : LevyFoundations.isCadlag f) (t : ℝ≥0) : ∃ C : ℝ, ∀ᶠ s in 𝓝 t, ‖f s‖ ≤ C := by
  obtain ⟨hr, l, hl⟩ := hf t
  have h1 : ∀ᶠ s in 𝓝[≥] t, ‖f s‖ < ‖f t‖ + 1 :=
    hr.norm.eventually_lt_const (by linarith)
  have h2 : ∀ᶠ s in 𝓝[<] t, ‖f s‖ < ‖l‖ + 1 :=
    hl.norm.eventually_lt_const (by linarith)
  refine ⟨max (‖f t‖ + 1) (‖l‖ + 1), ?_⟩
  rw [← nhdsLT_sup_nhdsGE t]
  exact Filter.eventually_sup.2 ⟨h2.mono fun s hs => hs.le.trans (le_max_right _ _),
    h1.mono fun s hs => hs.le.trans (le_max_left _ _)⟩

lemma tendsto_phi_joint {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (t0 : ℝ≥0) :
    Tendsto (fun p : ℝ≥0 × E => charFun (μ.map (X p.1)) p.2) (𝓝 (t0, 0)) (𝓝 1) := by
  have hrep : ∀ p : ℝ≥0 × E, charFun (μ.map (X p.1)) p.2 =
      ∫ ω, Complex.exp ((inner ℝ (X p.1 ω) p.2 : ℝ) * Complex.I) ∂μ := by
    intro p
    rw [charFun_apply, integral_map (hX p.1).aemeasurable (by fun_prop)]
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 ((t0, (0 : E))))
    (F := fun (p : ℝ≥0 × E) ω => Complex.exp ((inner ℝ (X p.1 ω) p.2 : ℝ) * Complex.I))
    (f := fun _ => (1 : ℂ)) (fun _ => 1)
    (Filter.Eventually.of_forall fun p => by
      exact (by have := hX p.1; fun_prop : Measurable fun ω =>
        Complex.exp ((inner ℝ (X p.1 ω) p.2 : ℝ) * Complex.I)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => Filter.Eventually.of_forall fun ω => by
      simp [Complex.norm_exp_ofReal_mul_I])
    (integrable_const _) ?_
  · have h1 : ∫ _ : Ω, (1 : ℂ) ∂μ = 1 := by simp
    rw [h1] at hlim
    simpa only [hrep] using hlim
  · filter_upwards [h.cadlag_ae] with ω hω
    obtain ⟨C, hC⟩ := cadlag_local_bound (fun t => X t ω) hω t0
    have hC' : ∀ᶠ p in 𝓝 ((t0, (0 : E))), ‖X p.1 ω‖ ≤ C :=
      (continuous_fst.tendsto (t0, (0 : E))).eventually hC
    have hn : Tendsto (fun p : ℝ≥0 × E => C * ‖p.2‖) (𝓝 ((t0, (0 : E)))) (𝓝 0) := by
      have := ((continuous_norm.comp continuous_snd).tendsto (t0, (0 : E))).const_mul C
      simpa using this
    have hin : Tendsto (fun p : ℝ≥0 × E => (inner ℝ (X p.1 ω) p.2 : ℝ)) (𝓝 ((t0, (0 : E)))) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hn
      filter_upwards [hC'] with p hp
      calc ‖(inner ℝ (X p.1 ω) p.2 : ℝ)‖ ≤ ‖X p.1 ω‖ * ‖p.2‖ := norm_inner_le_norm _ _
        _ ≤ C * ‖p.2‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    have hg : Continuous (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) := by fun_prop
    have := (hg.tendsto 0).comp hin
    simp only [Function.comp, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at this
    exact this


lemma uniform_small {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε, ∀ t ∈ Set.Icc (0 : ℝ≥0) 1,
      ‖charFun (μ.map (X t)) ξ - 1‖ < 1 / 2 := by
  refine isCompact_Icc.induction_on (p := fun s => ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε,
    ∀ t ∈ s, ‖charFun (μ.map (X t)) ξ - 1‖ < 1 / 2) ?_ ?_ ?_ ?_
  · exact ⟨1, one_pos, by simp⟩
  · rintro s t hst ⟨ε, hε, H⟩
    exact ⟨ε, hε, fun ξ hξ x hx => H ξ hξ x (hst hx)⟩
  · rintro s t ⟨ε1, h1, H1⟩ ⟨ε2, h2, H2⟩
    refine ⟨min ε1 ε2, lt_min h1 h2, fun ξ hξ x hx => ?_⟩
    rcases hx with hx | hx
    · exact H1 ξ (Metric.ball_subset_ball (min_le_left _ _) hξ) x hx
    · exact H2 ξ (Metric.ball_subset_ball (min_le_right _ _) hξ) x hx
  · intro x _
    have hlim := tendsto_phi_joint h hX x
    have hev : ∀ᶠ p in 𝓝 (x, (0 : E)), ‖charFun (μ.map (X p.1)) p.2 - 1‖ < 1 / 2 := by
      have := hlim.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
      filter_upwards [this] with p hp
      simpa [dist_eq_norm] using hp
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hev
    obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.1 hv
    exact ⟨u, mem_nhdsWithin_of_mem_nhds hu, ε, hε,
      fun ξ hξ t ht => huv (show (t, ξ) ∈ u ×ˢ v from ⟨ht, hεv hξ⟩)⟩

lemma core {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε, ∃ a : ℂ,
      (∀ t : ℝ≥0, charFun (μ.map (X t)) ξ = Complex.exp (((t : ℝ) : ℂ) * a)) ∧
      LevyFoundations.charExponent h ξ = a ∧ |a.im| < Real.pi := by
  obtain ⟨ε, hε, H⟩ := uniform_small h hX
  refine ⟨ε, hε, fun ξ hξ => ?_⟩
  set φ : ℝ≥0 → ℂ := fun s => charFun (μ.map (X s)) ξ with hφ
  have hcont : Continuous φ := cont_charFun h hX ξ
  have hadd : ∀ s u, φ (s + u) = φ s * φ u := fun s u => charFun_add h hX s u ξ
  have h0 : φ 0 = 1 := charFun_zero_time h ξ
  obtain ⟨a, δ, hδ, hall, hlog⟩ := exp_of_mult φ hcont hadd h0
  refine ⟨a, hall, ?_, ?_⟩
  · unfold LevyFoundations.charExponent
    apply Filter.Tendsto.limUnder_eq
    refine (tendsto_const_nhds (x := a)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
    have hs0 : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.1.ne'
    have := hlog s hs.1 hs.2.le
    simp only [hφ] at this
    rw [this]
    field_simp
  · by_contra hge
    rw [not_lt] at hge
    have hb : 0 < |a.im| := lt_of_lt_of_le Real.pi_pos hge
    have hts0 : 0 ≤ Real.pi / (2 * |a.im|) := by positivity
    have hts1 : Real.pi / (2 * |a.im|) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_pos]
    set tn : ℝ≥0 := ⟨Real.pi / (2 * |a.im|), hts0⟩ with htn
    have h1 : ‖φ tn - 1‖ < 1 / 2 := H ξ hξ tn ⟨zero_le', by
      show (tn : ℝ) ≤ 1
      exact hts1⟩
    have h2 : φ tn = Complex.exp (((Real.pi / (2 * |a.im|) : ℝ) : ℂ) * a) := hall tn
    have hcos : Real.cos (Real.pi / (2 * |a.im|) * a.im) = 0 := by
      rcases lt_or_gt_of_ne (abs_pos.1 hb) with hneg | hpos
      · rw [abs_of_neg hneg]
        have hne : a.im ≠ 0 := hneg.ne
        have : Real.pi / (2 * -a.im) * a.im = -(Real.pi / 2) := by field_simp
        rw [this, Real.cos_neg, Real.cos_pi_div_two]
      · rw [abs_of_pos hpos]
        have hne : a.im ≠ 0 := hpos.ne'
        have : Real.pi / (2 * a.im) * a.im = Real.pi / 2 := by field_simp
        rw [this, Real.cos_pi_div_two]
    have hre : (φ tn).re = 0 := by
      rw [h2, Complex.exp_re]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero] at hcos ⊢
      rw [hcos, mul_zero]
    have h3 : |(φ tn - 1).re| ≤ ‖φ tn - 1‖ := Complex.abs_re_le_norm _
    have h4 : (φ tn - 1).re = (φ tn).re - 1 := by simp
    rw [h4, hre] at h3
    simp at h3
    linarith

end Lv2Aux

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε,
      LevyFoundations.levyLocalCharExponent h hX ξ =
        LevyFoundations.charExponent h ξ := by
  obtain ⟨ε, hε, H⟩ := Lv2Aux.core h hX
  refine ⟨ε, hε, fun ξ hξ => ?_⟩
  obtain ⟨a, hall, hce, him⟩ := H ξ hξ
  have h1 : charFun (μ.map (X 1)) ξ = Complex.exp a := by
    have := hall 1
    simpa using this
  show Complex.log (charFun (μ.map (X 1)) ξ) = _
  rw [h1, hce]
  have hlt := abs_lt.1 him
  exact Complex.log_exp (by linarith [hlt.1]) (by linarith [hlt.2])
