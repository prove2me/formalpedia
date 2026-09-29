-- Prove2me | solution 1 for dlp_bernoulli_three_copy_triangle_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T17:51:32.517628+00:00
-- url     : https://prove2.me/submissions/58f1f66f-cb75-42f4-acfe-d419b6743ae1

import Theorems.Thm_bernoulli_powerset_event_prob_eq_product_measure
import Theorems.Thm_bernoulli_powerset_triple_event_prob_eq_product_measure
import Theorems.Thm_dlp_three_copy_triangle
import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Module.Basic
open MatrixCompletion
open scoped BigOperators Classical ENNReal
open MeasureTheory ProbabilityTheory

/-
Reduction of the powerset-Bernoulli 3-copy triangle (de la Peña–Montgomery-Smith
1995 Lemma 1, scalar abs form) onto three Proved children:

* `bernoulli_powerset_event_prob_eq_product_measure`  (single-copy bridge)
* `bernoulli_powerset_triple_event_prob_eq_product_measure`  (triple bridge)
* `dlp_three_copy_triangle`  (abstract Lemma 1 on `Measure.pi (Fin 3)`, V = ℝ)

Strategy: instantiate the abstract triangle at `V = ℝ`, `α = (Fin n1 × Fin n2) → Bool`,
`μ = bernMeasure p hp`, scalar statistic `f ω = Z (indicatorToFinset ω)`.  At V = ℝ,
`‖f g0‖ = |Z (i2f g0)|` and `‖f g0 + f g1‖ = |Z (i2f g0) + Z (i2f g1)|`.  The
single bridge marginalizes the LHS `Measure.pi (Fin 3)` quantity (coord 0) to the
single measure; the triple bridge transports the RHS `Measure.pi (Fin 3)` quantity
through the measure-preserving equiv `(Fin 3 → A) ≃ᵐ A × (A × A)` (composite of
`piFinSuccAbove 0` and `piFinTwo`) to the 3-fold product measure.
-/

theorem solution
    {n1 n2 : Nat} (p : NNReal) (hp : p ≤ 1)
    (Z : Finset (Fin n1 × Fin n2) → ℝ) (t : ℝ) :
    bernoulliEventProb (p : ℝ) (fun Omega => t ≤ |Z Omega|)
      ≤ 3 * bernoulliTripleEventProb (p : ℝ)
              (fun Omega1 Omega2 _Omega3 => 2 * t / 3 ≤ |Z Omega1 + Z Omega2|) := by
  classical
  set A := ((Fin n1 × Fin n2) → Bool) with hA
  set μ : Measure A := bernMeasure p hp with hμ
  have hprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set f : A → ℝ := fun ω => Z (indicatorToFinset ω) with hf
  have hfmeas : Measurable f := measurable_of_finite f
  rw [bernoulli_powerset_event_prob_eq_product_measure p hp (fun Omega => t ≤ |Z Omega|)]
  rw [bernoulli_powerset_triple_event_prob_eq_product_measure p hp
        (fun Omega1 Omega2 _Omega3 => 2 * t / 3 ≤ |Z Omega1 + Z Omega2|)]
  -- composite measure-preserving equiv  (Fin 3 → A) → A × (A × A)
  set e1 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => A) 0 with he1
  set e2 := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => A) with he2
  set e3 : (Fin 3 → A) ≃ᵐ A × (A × A) :=
    e1.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) e2) with he3
  set ν : Measure (Fin 3 → A) := Measure.pi (fun _ : Fin 3 => μ) with hν
  have hmp1 : MeasurePreserving e1 ν ((μ).prod (Measure.pi (fun j : Fin 2 => μ))) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) (0 : Fin 3)
    simpa [he1, hν] using this
  have hmp2 : MeasurePreserving e2 (Measure.pi (fun j : Fin 2 => μ)) (μ.prod μ) := by
    have := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
    simpa [he2] using this
  have hmpinner : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) e2)
      ((μ).prod (Measure.pi (fun j : Fin 2 => μ))) (μ.prod (μ.prod μ)) := by
    exact (MeasurePreserving.id μ).prod hmp2
  have hmp3 : MeasurePreserving e3 ν (μ.prod (μ.prod μ)) := by
    rw [he3]; exact hmp1.trans hmpinner
  -- apply the abstract triangle
  have htri := dlp_three_copy_triangle (V := ℝ) μ f hfmeas t
  rw [← hν] at htri
  have hnorm0 : ∀ g : Fin 3 → A, ‖f (g 0)‖ = |Z (indicatorToFinset (g 0))| := by
    intro g; rw [Real.norm_eq_abs, hf]
  have hnorm01 : ∀ g : Fin 3 → A, ‖f (g 0) + f (g 1)‖
      = |Z (indicatorToFinset (g 0)) + Z (indicatorToFinset (g 1))| := by
    intro g; rw [Real.norm_eq_abs, hf]
  -- LHS marginalization to the single measure (coord 0)
  have hLHS : ν.real {g : Fin 3 → A | t ≤ ‖f (g 0)‖}
      = μ.real {ω : A | t ≤ |Z (indicatorToFinset ω)|} := by
    have hev : MeasurePreserving (fun g : Fin 3 → A => g 0) ν μ := by
      have := measurePreserving_eval (μ := fun _ : Fin 3 => μ) (0 : Fin 3)
      simpa [hν] using this
    have hset : {g : Fin 3 → A | t ≤ ‖f (g 0)‖}
        = (fun g : Fin 3 → A => g 0) ⁻¹' {ω : A | t ≤ |Z (indicatorToFinset ω)|} := by
      ext g; simp only [Set.mem_preimage, Set.mem_setOf_eq]; rw [hnorm0 g]
    rw [hset]
    exact hev.measureReal_preimage
      (DiscreteMeasurableSpace.forall_measurableSet _).nullMeasurableSet
  -- RHS transport to the 3-fold product measure
  have hRHS : ν.real {g : Fin 3 → A | 2 * t / 3 ≤ ‖f (g 0) + f (g 1)‖}
      = (μ.prod (μ.prod μ)).real
          {ω : A × (A × A) |
            2 * t / 3 ≤ |Z (indicatorToFinset ω.1) + Z (indicatorToFinset ω.2.1)|} := by
    have hset : {g : Fin 3 → A | 2 * t / 3 ≤ ‖f (g 0) + f (g 1)‖}
        = e3 ⁻¹' {ω : A × (A × A) |
            2 * t / 3 ≤ |Z (indicatorToFinset ω.1) + Z (indicatorToFinset ω.2.1)|} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [hnorm01 g]
      have he : (e3 g).1 = g 0 ∧ (e3 g).2.1 = g 1 := by
        rw [he3]
        simp only [MeasurableEquiv.coe_trans, Function.comp_apply,
          he1, MeasurableEquiv.piFinSuccAbove_apply, he2]
        refine ⟨rfl, ?_⟩
        simp [MeasurableEquiv.prodCongr, Fin.tail]
      rw [he.1, he.2]
    rw [hset]
    exact hmp3.measureReal_preimage
      (DiscreteMeasurableSpace.forall_measurableSet _).nullMeasurableSet
  rw [hLHS, hRHS] at htri
  rw [← hμ]
  exact htri
