-- Prove2me | solution 1 for levy_foundations_poissonTimeCountIndependentBands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:24:28.310968+00:00
-- url     : https://prove2.me/submissions/4b19a5a6-beb7-4914-97d7-97929899c60a

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_prmIndependentFiniteFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! Ordered consecutive time bands are pairwise disjoint and finite in intensity. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × E) (A : Set E)
    (hd : LevyFoundations.IsPoissonPointFamily K X (volume.prod m) μ)
    (hA : MeasurableSet A) (hfin : m A < ⊤)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) :
    iIndepFun (fun (i : Fin n) ω =>
      LevyFoundations.poissonRandomMeasure K X ω
        (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)) μ := by
  let B : Fin n → Set (ℝ × E) :=
    fun i => Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A
  have hmeas : ∀ i, MeasurableSet (B i) := by
    intro i
    exact measurableSet_Ioc.prod hA
  have hfin' : ∀ i, (volume.prod m) (B i) < ⊤ := by
    intro i
    change (volume.prod m) (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A) < ⊤
    rw [Measure.prod_prod, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    change Disjoint (B i) (B j)
    rcases lt_or_gt_of_ne hij with h | h
    · change Disjoint
        (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)
        (Set.Ioc (t j.castSucc) (t j.succ) ×ˢ A)
      refine Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (ht ?_)) A A
      have hv : (i : ℕ) < (j : ℕ) := h
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
    · change Disjoint
        (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)
        (Set.Ioc (t j.castSucc) (t j.succ) ×ˢ A)
      apply Disjoint.symm
      refine Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (ht ?_)) A A
      have hv : (j : ℕ) < (i : ℕ) := h
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
  have hfamily := levy_foundations_prmIndependentFiniteFamily
    (volume.prod m) μ K X hd B hmeas hfin' hdisj
  simpa only [B] using hfamily
