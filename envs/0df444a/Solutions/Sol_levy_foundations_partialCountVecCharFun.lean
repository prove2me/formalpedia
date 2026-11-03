-- Prove2me | solution 1 for levy_foundations_partialCountVecCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:39:38.402824+00:00
-- url     : https://prove2.me/submissions/4bf4ce66-55c9-4c9e-ae5b-e71f42bc356b

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_prmPartialCount
import Definitions.Def_levy_foundations_prmPiece
import Theorems.Thm_levy_foundations_thinnedCountVecCharFun
import Theorems.Thm_levy_foundations_partialNextVecIndependent
import Theorems.Thm_levy_foundations_prmPartialCountSucc
import Theorems.Thm_levy_foundations_prmPartialCountMeasurable
import Theorems.Thm_levy_foundations_thinnedCountMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex

theorem solution
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι] [DecidableEq ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (n : ℕ) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) =>
      (LevyFoundations.prmPartialCount K X (A i) n ω : ℝ)) L =
    ∏ i, Complex.exp
      (↑(∑ k ∈ Finset.range (n + 1),
        (m (LevyFoundations.prmPiece m k ∩ A i)).toReal) *
        (Complex.exp (↑(L (Pi.single i 1)) * Complex.I) - 1))  := by
  induction n with
  | zero =>
    have h0 : (fun ω (i : ι) =>
        (LevyFoundations.prmPartialCount K X (A i) 0 ω : ℝ)) =
        fun ω (i : ι) =>
          (LevyFoundations.thinnedCount K X (A i) 0 ω : ℝ) := by
      funext ω i
      rw [LevyFoundations.prmPartialCount, Finset.sum_range_one]
    rw [h0, levy_foundations_thinnedCountVecCharFun m μ K X hd A hA hdisj 0 L]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  | succ n ih =>
    have mPn : Measurable (fun ω (i : ι) =>
        (LevyFoundations.prmPartialCount K X (A i) n ω : ℝ)) :=
      measurable_pi_lambda _ fun i => measurable_from_top.comp
        (levy_foundations_prmPartialCountMeasurable K X (A i) n
          hd.measurable_count hd.measurable_point (hA i))
    have mQn : Measurable (fun ω (i : ι) =>
        (LevyFoundations.thinnedCount K X (A i) (n + 1) ω : ℝ)) :=
      measurable_pi_lambda _ fun i => measurable_from_top.comp
        (levy_foundations_thinnedCountMeasurable K X (A i) (n + 1)
          (hd.measurable_count _) (hd.measurable_point _) (hA i))
    have hsucc : (fun ω (i : ι) =>
        (LevyFoundations.prmPartialCount K X (A i) (n + 1) ω : ℝ)) =
        fun ω => (fun i => (LevyFoundations.prmPartialCount K X (A i) n ω : ℝ))
          + fun i => (LevyFoundations.thinnedCount K X (A i) (n + 1) ω : ℝ) := by
      funext ω i
      simp only [Pi.add_apply]
      rw [levy_foundations_prmPartialCountSucc K X (A i) n ω, Nat.cast_add]
    rw [hsucc,
      IndepFun.charFunDual_map_fun_add_eq_mul
        mPn.aemeasurable mQn.aemeasurable
        (levy_foundations_partialNextVecIndependent m μ K X hd A hA n),
      Pi.mul_apply, ih,
      levy_foundations_thinnedCountVecCharFun m μ K X hd A hA hdisj (n + 1) L,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ
      (fun k => (m (LevyFoundations.prmPiece m k ∩ A i)).toReal) (n + 1),
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
