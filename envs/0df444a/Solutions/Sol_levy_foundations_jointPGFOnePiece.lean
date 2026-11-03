-- Prove2me | solution 1 for levy_foundations_jointPGFOnePiece
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:22:48.454831+00:00
-- url     : https://prove2.me/submissions/93199c8a-0675-4db9-a266-79fb241df67d

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_thinnedCount
import Theorems.Thm_levy_foundations_prodIteConstCard
import Theorems.Thm_levy_foundations_prodIteDisjoint
import Theorems.Thm_levy_foundations_poissonPieceProdPGF
import Theorems.Thm_levy_foundations_prmPieceLawMassBridge
import Theorems.Thm_levy_foundations_prmPieceLawProb

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex

theorem solution
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (k : ℕ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∫ ω, ∏ i, (z i) ^ (LevyFoundations.thinnedCount K X (A i) k ω) ∂μ =
      ∏ i, Complex.exp ((m (LevyFoundations.prmPiece m k ∩ A i)).toReal * (z i - 1)) := by
  classical
  haveI : IsProbabilityMeasure (LevyFoundations.prmPieceLaw m k) :=
    levy_foundations_prmPieceLawProb m k
  set w : E → ℂ := fun x => ∏ i, (if x ∈ A i then z i else 1) with hw_def
  have hwmeas : Measurable w :=
    Finset.measurable_prod _ fun i _ =>
      Measurable.ite (hA i) measurable_const measurable_const
  have hwbdd : ∀ x, ‖w x‖ ≤ 1 := by
    intro x
    rw [hw_def, norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
    split_ifs
    · exact hz i
    · simp
  have hprod : ∀ ω, ∏ i, (z i) ^ (LevyFoundations.thinnedCount K X (A i) k ω) =
      ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    simp only [hw_def]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [levy_foundations_prodIteConstCard
      (Finset.range (K k ω)) (fun n => X k n ω ∈ A i) (z i)]
    rfl
  simp_rw [hprod]
  rw [levy_foundations_poissonPieceProdPGF m μ K X hd k w hwmeas hwbdd]
  have hint : ∫ x, w x ∂(LevyFoundations.prmPieceLaw m k) =
      1 + ∑ i, (z i - 1) *
        ((LevyFoundations.prmPieceLaw m k).real (A i)) := by
    have hwrw : w = fun x => (1 : ℂ) +
        ∑ i, (A i).indicator (fun _ => z i - 1) x := by
      funext x
      rw [hw_def]
      exact levy_foundations_prodIteDisjoint A hdisj z x
    have hi : ∀ i, Integrable (fun x =>
        (A i).indicator (fun _ => z i - 1) x)
        (LevyFoundations.prmPieceLaw m k) :=
      fun i => (integrable_const (z i - 1)).indicator (hA i)
    have hone : ∫ _ : E, (1 : ℂ)
        ∂(LevyFoundations.prmPieceLaw m k) = 1 := by simp
    rw [hwrw, integral_add (integrable_const 1)
      (integrable_finsetSum _ fun i _ => hi i),
      integral_finsetSum _ (fun i _ => hi i), hone]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const (z i - 1) (hA i)]
    rw [Complex.real_smul]
    ring
  rw [hint, show ((m (LevyFoundations.prmPiece m k)).toReal : ℂ) *
      ((1 + ∑ i, (z i - 1) *
        ((LevyFoundations.prmPieceLaw m k).real (A i))) - 1) =
      ∑ i, (((m (LevyFoundations.prmPiece m k)).toReal *
        (LevyFoundations.prmPieceLaw m k).real (A i) : ℝ) : ℂ) *
          (z i - 1) from ?_]
  · rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [levy_foundations_prmPieceLawMassBridge m k (hA i)]
  · push_cast
    rw [add_sub_cancel_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
