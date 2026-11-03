-- Prove2me | solution 1 for levy_foundations_thinnedCountVecCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:31:12.466993+00:00
-- url     : https://prove2.me/submissions/8386fe90-88e1-46d7-9e55-6d916d858b7c

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_thinnedCount
import Theorems.Thm_levy_foundations_thinnedCountMeasurable
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPiece
import Theorems.Thm_levy_foundations_poissonPieceProdPGF
import Theorems.Thm_levy_foundations_prmPieceLawMassBridge
import Theorems.Thm_levy_foundations_jointPGFOnePiece
import Theorems.Thm_levy_foundations_piDualApply

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
    (k : ℕ) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) =>
      (LevyFoundations.thinnedCount K X (A i) k ω : ℝ)) L =
    ∏ i, Complex.exp ((m (LevyFoundations.prmPiece m k ∩ A i)).toReal *
      (Complex.exp (↑(L (Pi.single i 1)) * Complex.I) - 1)) := by
  have hT : ∀ i, Measurable (LevyFoundations.thinnedCount K X (A i) k) :=
    fun i => levy_foundations_thinnedCountMeasurable K X (A i) k
      (hd.measurable_count k) (hd.measurable_point k) (hA i)
  rw [charFunDual_apply, integral_map
    (φ := fun ω (i : ι) => (LevyFoundations.thinnedCount K X (A i) k ω : ℝ))
    (measurable_pi_lambda _ fun i =>
      (measurable_from_top.comp (hT i))).aemeasurable (by fun_prop)]
  have hpow : ∀ ω, Complex.exp
      (↑(L fun i => (LevyFoundations.thinnedCount K X (A i) k ω : ℝ)) *
        Complex.I) =
      ∏ i, (Complex.exp (↑(L (Pi.single i 1)) * Complex.I)) ^
        (LevyFoundations.thinnedCount K X (A i) k ω) := by
    intro ω
    rw [levy_foundations_piDualApply L
      (fun i => (LevyFoundations.thinnedCount K X (A i) k ω : ℝ)),
      show (↑(∑ i, (LevyFoundations.thinnedCount K X (A i) k ω : ℝ) *
        L (Pi.single i 1)) : ℂ) * Complex.I =
        ∑ i, ↑(LevyFoundations.thinnedCount K X (A i) k ω) *
          (↑(L (Pi.single i 1)) * Complex.I) from by
            push_cast
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring,
      Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => Complex.exp_nat_mul _ _
  simp_rw [hpow]
  exact levy_foundations_jointPGFOnePiece m μ K X hd A hA hdisj k
    (fun i => Complex.exp (↑(L (Pi.single i 1)) * Complex.I))
    (fun i => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
