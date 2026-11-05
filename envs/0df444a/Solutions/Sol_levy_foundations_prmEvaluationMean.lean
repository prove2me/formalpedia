-- Prove2me | solution 1 for levy_foundations_prmEvaluationMean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:02:02.645118+00:00
-- url     : https://prove2.me/submissions/dea935b1-33df-4faa-941e-64605770bffd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Theorems.Thm_levy_foundations_prmEvaluationMeanFinite
import Theorems.Thm_levy_foundations_measurablePRMEval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ ω, LevyFoundations.poissonRandomMeasure K X ω A ∂μ = m A := by
  let S : ℕ → Set E := fun n => A ∩ spanningSets m n
  have hSmono : Monotone S := by
    intro i j hij x hx
    exact ⟨hx.1, (monotone_spanningSets m hij) hx.2⟩
  have hSmeas (n : ℕ) : MeasurableSet (S n) :=
    hA.inter (measurableSet_spanningSets m n)
  have hSfin (n : ℕ) : m (S n) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      (measure_spanningSets_lt_top m n)
  have hCover : (⋃ n, S n) = A := by
    dsimp [S]
    rw [← Set.inter_iUnion, iUnion_spanningSets m, Set.inter_univ]
  have hN (ω : Ω) :
      LevyFoundations.poissonRandomMeasure K X ω A =
        ⨆ n, LevyFoundations.poissonRandomMeasure K X ω (S n) := by
    rw [← hCover]
    exact hSmono.measure_iUnion
  have hM : m A = ⨆ n, m (S n) := by
    rw [← hCover]
    exact hSmono.measure_iUnion
  have hEval (n : ℕ) : Measurable
      (fun ω => LevyFoundations.poissonRandomMeasure K X ω (S n)) :=
    levy_foundations_measurablePRMEval K X
      hd.measurable_count hd.measurable_point (hSmeas n)
  have hMon (i j : ℕ) (hij : i ≤ j) (ω : Ω) :
      LevyFoundations.poissonRandomMeasure K X ω (S i) ≤
        LevyFoundations.poissonRandomMeasure K X ω (S j) :=
    measure_mono (hSmono hij)
  calc
    ∫⁻ ω, LevyFoundations.poissonRandomMeasure K X ω A ∂μ =
        ∫⁻ ω, ⨆ n, LevyFoundations.poissonRandomMeasure K X ω (S n) ∂μ := by
      congr 1
      funext ω
      exact hN ω
    _ = ⨆ n, ∫⁻ ω, LevyFoundations.poissonRandomMeasure K X ω (S n) ∂μ := by
      rw [lintegral_iSup hEval hMon]
    _ = ⨆ n, m (S n) := by
      congr 1
      funext n
      exact levy_foundations_prmEvaluationMeanFinite m μ K X hd (hSmeas n) (hSfin n)
    _ = m A := hM.symm
