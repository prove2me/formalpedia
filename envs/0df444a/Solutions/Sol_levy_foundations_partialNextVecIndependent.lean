-- Prove2me | solution 1 for levy_foundations_partialNextVecIndependent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:27:41.645902+00:00
-- url     : https://prove2.me/submissions/e3f1ef24-ba15-4e60-8b5f-152e1f7863b4

import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_prmPartialCount
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_pointFamilySplitIndep
import Theorems.Thm_levy_foundations_measurableFilterCard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} {ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (n : ℕ) :
    IndepFun
      (fun ω (i : ι) => (LevyFoundations.prmPartialCount K X (A i) n ω : ℝ))
      (fun ω (i : ι) => (LevyFoundations.thinnedCount K X (A i) (n + 1) ω : ℝ))
      μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ))
      (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1))
      (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;> simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;>
      simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
        ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := levy_foundations_pointFamilySplitIndep
    m μ K X hd φ ψ hφ_inj hψ_inj hST
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ,
      LevyFoundations.pointFamilyIndexType E (φ i)) → (ι → ℕ) :=
    fun g i => ∑ k : Fin (n + 1),
      ((Finset.range (g (Sum.inl k))).filter
        (fun n' => g (Sum.inr (k, n')) ∈ A i)).card with hG_def
  set H : (∀ j : Unit ⊕ ℕ,
      LevyFoundations.pointFamilyIndexType E (ψ j)) → (ι → ℕ) :=
    fun g i =>
      ((Finset.range (g (Sum.inl ()))).filter
        (fun n' => g (Sum.inr n') ∈ A i)).card with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact measurable_pi_lambda _ fun i =>
      Finset.measurable_sum _ fun k _ =>
        levy_foundations_measurableFilterCard
          (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) →
            LevyFoundations.pointFamilyIndexType E (φ i))
          (A i) (hA i)
          (fun g => g (Sum.inl k))
          (fun n' g => g (Sum.inr (k, n')))
          (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H := by
    rw [hH_def]
    exact measurable_pi_lambda _ fun i =>
      levy_foundations_measurableFilterCard
        (D := (j : Unit ⊕ ℕ) →
          LevyFoundations.pointFamilyIndexType E (ψ j))
        (A i) (hA i)
        (fun g => g (Sum.inl ()))
        (fun n' g => g (Sum.inr n'))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i =>
      LevyFoundations.pointFamilyCombined K X (φ i) ω) =
      fun ω (i : ι) => (LevyFoundations.prmPartialCount K X (A i) n ω : ℕ) := by
    funext ω i
    simp only [hG_def]
    unfold LevyFoundations.prmPartialCount
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => LevyFoundations.thinnedCount K X (A i) j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j =>
      LevyFoundations.pointFamilyCombined K X (ψ j) ω) =
      fun ω (i : ι) => (LevyFoundations.thinnedCount K X (A i) (n + 1) ω : ℕ) := by
    funext ω i
    rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rw [hGeq, hHeq] at key
  have hcast := key.comp
    (φ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (ψ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (measurable_pi_lambda _ fun i =>
      measurable_from_top.comp (measurable_pi_apply i))
    (measurable_pi_lambda _ fun i =>
      measurable_from_top.comp (measurable_pi_apply i))
  simpa only [Function.comp_def] using hcast
