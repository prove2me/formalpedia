-- Prove2me | solution 1 for hoeffding_one_sided_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:34:49.052652+00:00
-- url     : https://prove2.me/submissions/052068c4-96c5-4c4a-bf41-3bda216b1e3b

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
section
@[expose] public section
universe u v
open MeasureTheory ENNReal
private theorem subgaussian_sum_tail {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (m : ℕ) (t : ℝ) (ht : 0 < t) (g : X → ℝ) (a : ℝ)
    (h_g_meas : Measurable g) (h_g_bound : ∀ x : X, g x ∈ Set.Icc a (a + 1))
    (h_int_g : ∫ x, g x ∂D = 0) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => D)).real
      {xs : Fin m → X | ↑m * t ≤ ∑ i : Fin m, g (xs i)}
    ≤ Real.exp (-2 * ↑m * t ^ 2) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  have : MeasureTheory.IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have h_g_subG : ProbabilityTheory.HasSubgaussianMGF g ((1 / 2 : NNReal) ^ 2) D := by
    have h_param : (‖(a + 1) - a‖₊ / 2) ^ 2 = ((1 : NNReal) / 2) ^ 2 := by
      congr 1
      rw [show (a + 1) - a = (1 : ℝ) from by ring]
      simp [nnnorm_one]
    rw [← h_param]
    exact ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      h_g_meas.aemeasurable (Filter.Eventually.of_forall h_g_bound) h_int_g
  have h_indep : ProbabilityTheory.iIndepFun
      (m := fun _ => inferInstance)
      (fun i (xs : Fin m → X) => g (xs i)) μ := by
    rw [hμ_def]
    exact ProbabilityTheory.iIndepFun_pi (fun _ => h_g_meas.aemeasurable)
  have h_subG_each : ∀ i : Fin m, ProbabilityTheory.HasSubgaussianMGF
      (fun xs : Fin m → X => g (xs i)) ((1 / 2 : NNReal) ^ 2) μ := fun i =>
    have : ProbabilityTheory.HasSubgaussianMGF
        (g ∘ fun (xs : Fin m → X) => xs i) ((1 / 2 : NNReal) ^ 2) μ :=
      ProbabilityTheory.HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable
        (by rw [hμ_def, MeasureTheory.measurePreserving_eval _ i |>.map_eq]; exact h_g_subG)
    this
  have h_eps_pos : (0 : ℝ) ≤ ↑m * t := by positivity
  have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    h_indep (c := fun _ => (1 / 2 : NNReal) ^ 2) (s := Finset.univ)
    (fun i _ => h_subG_each i) h_eps_pos
  have h_sum_c : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1 / 2 : NNReal) ^ 2 : NNReal)) =
      ↑m * (1 / 2 : NNReal) ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h_sum_c] at h_hoeff
  rwa [show Real.exp (-(↑m * t) ^ 2 / (2 * ↑(↑m * (1 / 2 : NNReal) ^ 2 : NNReal))) =
      Real.exp (-2 * ↑m * t ^ 2) from by
    congr 1
    push_cast
    field_simp] at h_hoeff
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1)
    (hmeas : MeasurableSet {x | h x ≠ c x}) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) ≥ TrueErrorReal X h c D + t}
    ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set p := TrueErrorReal X h c D with hp_def
  set indicator : X → ℝ := fun x => zeroOneLoss Bool (h x) (c x) with hind_def
  set Z : Fin m → (Fin m → X) → ℝ := fun i xs => indicator (xs i) - p with hZ_def
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set S := {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) ≥ p + t} with hS_def
  have h_set_sub : S ⊆ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} := by
    intro xs hxs
    simp only [Set.mem_ofPred_eq] at hxs ⊢
    simp only [hZ_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [hS_def, Set.mem_ofPred_eq, EmpiricalError,
      Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hxs
    have h_div : p + t ≤ (∑ i : Fin m, zeroOneLoss Bool (h (xs i)) (c (xs i))) / (m : ℝ) := hxs
    rw [le_div_iff₀ hm_pos] at h_div
    linarith
  calc μ S
      ≤ μ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} :=
        MeasureTheory.measure_mono h_set_sub
    _ = ENNReal.ofReal (μ.real {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs}) := by
        rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        set g : X → ℝ := fun x => indicator x - p with hg_def
        have h_ind_bound : ∀ x : X, indicator x ∈ Set.Icc (0 : ℝ) 1 := fun x => by
          simp only [hind_def, zeroOneLoss, Set.mem_Icc]
          split <;> norm_num
        have h_g_bound : ∀ x : X, g x ∈ Set.Icc (-p) ((-p) + 1) := fun x => by
          simp only [hg_def, Set.mem_Icc]
          constructor <;> linarith [(h_ind_bound x).1, (h_ind_bound x).2]
        have h_ind_meas : Measurable indicator := by
          simp only [hind_def, zeroOneLoss]
          exact Measurable.ite (by convert hmeas.compl using 1; ext x; simp)
            measurable_const measurable_const
        have h_g_meas : Measurable g := h_ind_meas.sub measurable_const
        have h_int_ind : ∫ x, indicator x ∂D = p := by
          simp only [hind_def, zeroOneLoss, hp_def, TrueErrorReal, TrueError]
          rw [show (fun x => if h x = c x then (0 : ℝ) else 1) =
              Set.indicator {x | h x ≠ c x} 1 from by ext x; simp [Set.indicator],
            integral_indicator_one hmeas]
          simp only [Measure.real]
        have h_int_g : ∫ x, g x ∂D = 0 := by
          simp only [hg_def]
          rw [integral_sub
            (Integrable.of_mem_Icc 0 1 h_ind_meas.aemeasurable
              (Filter.Eventually.of_forall h_ind_bound))
            (integrable_const p)]
          simp [h_int_ind]
        exact subgaussian_sum_tail D m t ht g (-p) h_g_meas h_g_bound h_int_g
