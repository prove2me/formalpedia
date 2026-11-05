-- Prove2me | solution 1 for levy_foundations_prmIndependent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:13:42.990726+00:00
-- url     : https://prove2.me/submissions/adcdf324-5102-4aae-ad5c-361534bf0e03

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Theorems.Thm_levy_foundations_prmIndependentFiniteFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-! Derive two-set independent scattering from the accepted finite-family theorem. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) :
    IndepFun
      (fun ω => LevyFoundations.poissonRandomMeasure K X ω A)
      (fun ω => LevyFoundations.poissonRandomMeasure K X ω B) μ := by
  let C : Fin 2 → Set E := fun i => if i = 0 then A else B
  have hmeas : ∀ i, MeasurableSet (C i) := by
    intro i
    fin_cases i
    · simpa [C] using hA
    · simpa [C] using hB
  have hfin : ∀ i, m (C i) < ⊤ := by
    intro i
    fin_cases i
    · simpa [C] using hfinA
    · simpa [C] using hfinB
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint (C 0) (C 1)
      simpa [C] using hAB
    · change Disjoint (C 1) (C 0)
      simpa [C] using hAB.symm
    · exact (hij rfl).elim
  have hall := levy_foundations_prmIndependentFiniteFamily m μ K X hd C hmeas hfin hdisj
  have h01 := hall.indepFun (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  simpa [C] using h01
