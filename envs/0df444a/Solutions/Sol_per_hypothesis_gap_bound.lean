-- Prove2me | solution 1 for per_hypothesis_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:51.435798+00:00
-- url     : https://prove2.me/submissions/7fb69ed5-2a93-43f2-aa74-0039426b74ed

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (hmeas_h : Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
    (μ.prod μ)
      {p : (Fin m → X) × (Fin m → X) |
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by
  intro μ
  set indicator : X → ℝ := fun x => zeroOneLoss Bool (h x) (c x) with hind_def
  set g : X × X → ℝ := fun pair => indicator pair.2 - indicator pair.1 with hg_def
  set ν := D.prod D with hν_def
  set π := MeasureTheory.Measure.pi (fun _ : Fin m => ν) with hπ_def
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set equiv := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m) with hequiv_def
  have h_mp : MeasurePreserving (⇑equiv) π (μ.prod μ) := by
    rw [hπ_def, hν_def]
    show MeasurePreserving (⇑equiv) (Measure.pi fun _ => D.prod D) (μ.prod μ)
    exact measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
  set S_sum := {z : Fin m → X × X | (↑m * (ε / 2) : ℝ) ≤ ∑ i : Fin m, g (z i)}
    with hS_sum_def
  set S := {p : (Fin m → X) × (Fin m → X) |
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hS_def
  have h_preimage_sub : equiv ⁻¹' S ⊆ S_sum := by
    intro z hz
    simp only [hS_def, hS_sum_def, Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
    unfold EmpiricalError at hz
    simp only [Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hz
    have h_fst : (equiv z).1 = fun i => (z i).1 := by
      ext i; simp [hequiv_def, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
    have h_snd : (equiv z).2 = fun i => (z i).2 := by
      ext i; simp [hequiv_def, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
    rw [h_fst, h_snd] at hz
    simp only [hg_def, hind_def]
    rw [ge_iff_le, div_sub_div_same] at hz
    rw [le_div_iff₀ hm_pos] at hz
    rw [← Finset.sum_sub_distrib] at hz
    linarith
  have h_bound1 : (μ.prod μ) S ≤ π S_sum := by
    have h_eq_preimage : (μ.prod μ) S = π (equiv ⁻¹' S) := by
      rw [← h_mp.map_eq]; exact equiv.map_apply S
    rw [h_eq_preimage]
    exact MeasureTheory.measure_mono h_preimage_sub
  calc (μ.prod μ) S
      ≤ π S_sum := h_bound1
    _ = ENNReal.ofReal (π.real S_sum) := by rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by
        apply ENNReal.ofReal_le_ofReal
        have hmeas_ne : MeasurableSet {a : X | h a ≠ c a} :=
          (measurableSet_eq_fun hmeas_h hc_meas).compl
        have h_ind_meas : Measurable indicator := by
          simp only [hind_def, zeroOneLoss]
          exact Measurable.ite (by convert hmeas_ne.compl using 1; ext x; simp)
            measurable_const measurable_const
        have h_g_meas : Measurable g :=
          (h_ind_meas.comp measurable_snd).sub (h_ind_meas.comp measurable_fst)
        have h_ind_bound : ∀ x : X, indicator x ∈ Set.Icc (0 : ℝ) 1 := fun x => by
          simp only [hind_def, zeroOneLoss, Set.mem_Icc]
          split <;> norm_num
        have h_g_bound : ∀ pair : X × X, g pair ∈ Set.Icc (-1 : ℝ) 1 := fun pair => by
          simp only [hg_def, Set.mem_Icc]
          constructor <;> linarith [(h_ind_bound pair.1).1, (h_ind_bound pair.1).2,
            (h_ind_bound pair.2).1, (h_ind_bound pair.2).2]
        have h_int_g : ∫ pair, g pair ∂ν = 0 := by
          have h_g_int : Integrable g ν :=
            hν_def ▸ Integrable.of_mem_Icc (-1) 1
              h_g_meas.aemeasurable (Filter.Eventually.of_forall h_g_bound)
          rw [hν_def, MeasureTheory.integral_prod (f := g) (by rwa [hν_def] at h_g_int)]
          have h_ind_int : Integrable indicator D :=
            Integrable.of_mem_Icc 0 1 h_ind_meas.aemeasurable
              (Filter.Eventually.of_forall h_ind_bound)
          have h_inner : ∀ a, ∫ b, g (a, b) ∂D = ∫ x, indicator x ∂D - indicator a := by
            intro a
            simp only [hg_def]
            rw [MeasureTheory.integral_sub h_ind_int (integrable_const _)]
            simp [MeasureTheory.integral_const]
          simp_rw [h_inner]
          rw [MeasureTheory.integral_sub (integrable_const _) h_ind_int]
          simp [MeasureTheory.integral_const]
        have h_g_subG : ProbabilityTheory.HasSubgaussianMGF g (1 : NNReal) ν := by
          have h_param : (‖(1:ℝ) - (-1:ℝ)‖₊ / 2) ^ 2 = (1 : NNReal) := by
            have h2 : (1:ℝ) - (-1:ℝ) = 2 := by ring
            rw [h2, Real.nnnorm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
            ext
            simp
          rw [← h_param]
          exact ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
            h_g_meas.aemeasurable (Filter.Eventually.of_forall h_g_bound) h_int_g
        have h_indep : ProbabilityTheory.iIndepFun
            (m := fun _ => inferInstance)
            (fun i (z : Fin m → X × X) => g (z i)) π := by
          rw [hπ_def]
          exact ProbabilityTheory.iIndepFun_pi (fun _ => h_g_meas.aemeasurable)
        have h_subG_each : ∀ i : Fin m, ProbabilityTheory.HasSubgaussianMGF
            (fun z : Fin m → X × X => g (z i)) 1 π := fun i =>
          have : ProbabilityTheory.HasSubgaussianMGF
              (g ∘ fun (z : Fin m → X × X) => z i) 1 π :=
            ProbabilityTheory.HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable
              (by rw [hπ_def,
                      (MeasureTheory.measurePreserving_eval (fun _ : Fin m => ν) i).map_eq]
                  exact h_g_subG)
          this
        have h_eps_pos : (0 : ℝ) ≤ ↑m * (ε / 2) := by positivity
        have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          h_indep (c := fun _ => (1 : NNReal)) (s := Finset.univ)
          (fun i _ => h_subG_each i) h_eps_pos
        have h_sum_c : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1 : NNReal) : NNReal)) =
            (↑m : NNReal) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [h_sum_c] at h_hoeff
        suffices h_exp : Real.exp (-(↑m * (ε / 2)) ^ 2 / (2 * ↑(↑m : NNReal))) =
            Real.exp (-(↑m * ε ^ 2 / 8)) by
          rw [h_exp] at h_hoeff; exact h_hoeff
        congr 1; push_cast; field_simp; ring
