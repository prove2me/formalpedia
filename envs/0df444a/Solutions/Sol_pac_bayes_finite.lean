-- Prove2me | solution 1 for pac_bayes_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:58.111465+00:00
-- url     : https://prove2.me/submissions/dcad34f6-ec43-4263-a483-2a2618c5edaf

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PACBayes
public import Theorems.Thm_pac_bayes_all_hypotheses
section
@[expose] public section
universe u
open MeasureTheory Finset
private lemma jensen_sqrt_finpmf {H : Type*} [Fintype H]
    (Q : FinitePMF H) (f : H → ℝ) (hf : ∀ h, 0 ≤ f h) :
    ∑ h : H, Q.prob h * Real.sqrt (f h) ≤
    Real.sqrt (∑ h : H, Q.prob h * f h) := by
  -- Via the variance identity ∑ q_h (√f_h - c)² ≥ 0 with c = ∑ q_h √f_h,
  -- which expands to c² ≤ ∑ q_h f_h (Cauchy-Schwarz).
  have h_sum_nonneg : 0 ≤ ∑ h : H, Q.prob h * Real.sqrt (f h) := by
    apply Finset.sum_nonneg; intro h _
    exact mul_nonneg (Q.prob_nonneg h) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq h_sum_nonneg]
  apply Real.sqrt_le_sqrt
  set c := ∑ h : H, Q.prob h * Real.sqrt (f h)
  have h_var_nonneg : 0 ≤ ∑ h : H, Q.prob h * (Real.sqrt (f h) - c) ^ 2 :=
    Finset.sum_nonneg (fun h _ => mul_nonneg (Q.prob_nonneg h) (sq_nonneg _))
  suffices h_sq_le : c ^ 2 ≤ ∑ h : H, Q.prob h * f h by
    linarith
  have h_expand_term : ∀ h : H, Q.prob h * (Real.sqrt (f h) - c) ^ 2 =
      Q.prob h * f h - 2 * Q.prob h * Real.sqrt (f h) * c + Q.prob h * c ^ 2 := by
    intro h
    have hsq : Real.sqrt (f h) * Real.sqrt (f h) = f h := Real.mul_self_sqrt (hf h)
    nlinarith [sq_nonneg (Real.sqrt (f h) - c), Q.prob_nonneg h, sq_nonneg c, hsq]
  have h_sum_qf : ∑ h : H, Q.prob h * (Real.sqrt (f h) - c) ^ 2 =
      ∑ h : H, (Q.prob h * f h - 2 * Q.prob h * Real.sqrt (f h) * c + Q.prob h * c ^ 2) := by
    congr 1; ext h; exact h_expand_term h
  rw [h_sum_qf, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h_var_nonneg
  -- ∑ 2 * Q.prob h * √(f h) * c = 2 * c * c
  have h_sum_mid : ∑ h : H, 2 * Q.prob h * Real.sqrt (f h) * c = 2 * c * c := by
    simp_rw [show ∀ h : H, 2 * Q.prob h * Real.sqrt (f h) * c =
      c * (Q.prob h * Real.sqrt (f h)) * 2 from fun h => by ring]
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  -- ∑ Q.prob h * c² = c²
  have h_sum_tail : ∑ h : H, Q.prob h * c ^ 2 = c ^ 2 := by
    simp_rw [show ∀ h : H, Q.prob h * c ^ 2 = c ^ 2 * Q.prob h from fun h => by ring]
    rw [← Finset.mul_sum, Q.prob_sum_one, mul_one]
  rw [h_sum_mid, h_sum_tail] at h_var_nonneg
  linarith [sq_nonneg c]
private lemma gibbs_bound_of_pointwise {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (hs : H → Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X)
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (S : Fin m → X)
    (hgood : ∀ h : H,
      TrueErrorReal X (hs h) c D ≤
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)))
    (Q : FinitePMF H) :
    gibbsError Q hs c D ≤
      gibbsEmpError Q hs c S +
      Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) := by
  unfold gibbsError gibbsEmpError expectFinitePMF
  set g := fun h : H => Real.log (1 / (P.prob h * δ)) / (2 * ↑m)
  have h_step1 : ∑ h : H, Q.prob h * TrueErrorReal X (hs h) c D ≤
      ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h)
        (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
      ∑ h : H, Q.prob h * Real.sqrt (g h) := by
    have : ∀ h : H, Q.prob h * TrueErrorReal X (hs h) c D ≤
        Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Q.prob h * Real.sqrt (g h) := by
      intro h; rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hgood h) (Q.prob_nonneg h)
    calc ∑ h : H, Q.prob h * TrueErrorReal X (hs h) c D
        ≤ ∑ h : H, (Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
            (zeroOneLoss Bool) + Q.prob h * Real.sqrt (g h)) :=
          Finset.sum_le_sum (fun h _ => this h)
      _ = _ := Finset.sum_add_distrib
  have hg_nonneg : ∀ h : H, 0 ≤ g h := by
    intro h; apply div_nonneg _ (by positivity)
    apply Real.log_nonneg; rw [le_div_iff₀ (mul_pos (hP_pos h) hδ)]
    simp only [one_mul]
    have : P.prob h ≤ 1 :=
      le_trans (Finset.single_le_sum (fun i _ => P.prob_nonneg i) (Finset.mem_univ h))
        (le_of_eq P.prob_sum_one)
    nlinarith
  have h_jensen := jensen_sqrt_finpmf Q g hg_nonneg
  have h_sum_g : ∑ h : H, Q.prob h * g h =
      (crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m) := by
    simp only [g]
    simp_rw [mul_div_assoc']
    rw [← Finset.sum_div]
    congr 1
    unfold crossEntropyFinitePMF
    have h_split : ∀ h : H, Q.prob h * Real.log (1 / (P.prob h * δ)) =
        (if Q.prob h = 0 then 0 else Q.prob h * Real.log (1 / P.prob h)) +
        Q.prob h * Real.log (1 / δ) := by
      intro h
      by_cases hq : Q.prob h = 0
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        rw [show (1 : ℝ) / (P.prob h * δ) = (1 / P.prob h) * (1 / δ) from by ring]
        rw [Real.log_mul (ne_of_gt (div_pos one_pos (hP_pos h)))
          (ne_of_gt (div_pos one_pos hδ))]
        ring
    simp_rw [h_split, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul, Q.prob_sum_one, one_mul]
  have h_sqrt_eq : Real.sqrt (∑ h : H, Q.prob h * g h) =
      Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) := by
    rw [h_sum_g]
  calc ∑ h : H, Q.prob h * TrueErrorReal X (hs h) c D
      ≤ ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
          (zeroOneLoss Bool) +
        ∑ h : H, Q.prob h * Real.sqrt (g h) := h_step1
    _ ≤ ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
          (zeroOneLoss Bool) +
        Real.sqrt (∑ h : H, Q.prob h * g h) := by linarith [h_jensen]
    _ = ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
          (zeroOneLoss Bool) +
        Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) := by
        rw [h_sqrt_eq]
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Finset
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        ∀ (Q : FinitePMF H),
          gibbsError Q hs c D ≤
            gibbsEmpError Q hs c S +
            Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) }
      ≥ ENNReal.ofReal (1 - δ) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  set AllHyp := { S : Fin m → X |
    ∀ h : H,
      TrueErrorReal X (hs h) c D ≤
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
  set PBEvent := { S : Fin m → X |
    ∀ (Q : FinitePMF H),
      gibbsError Q hs c D ≤
        gibbsEmpError Q hs c S +
        Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) }
  -- AllHyp ⊆ PBEvent (deterministic implication)
  have h_sub : AllHyp ⊆ PBEvent := by
    intro S hS Q
    exact gibbs_bound_of_pointwise hs c D P hP_pos m hm δ hδ hδ1 S hS Q
  calc μ PBEvent
      ≥ μ AllHyp := μ.mono h_sub
    _ ≥ ENNReal.ofReal (1 - δ) :=
        pac_bayes_all_hypotheses D c hc_meas hs hhs_meas P hP_pos m hm δ hδ hδ1
