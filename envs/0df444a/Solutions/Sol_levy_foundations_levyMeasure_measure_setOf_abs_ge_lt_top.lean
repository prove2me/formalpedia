-- Prove2me | solution 1 for levy_foundations_levyMeasure_measure_setOf_abs_ge_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:53.177183+00:00
-- url     : https://prove2.me/submissions/d5b3b3bd-0aba-4ff4-bb41-a7e19297134c

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory ENNReal Set
open scoped NNReal ENNReal

theorem solution
    {ν : Measure ℝ} (hν : LevyFoundations.isLevyMeasure ν)
    {ε : ℝ} (hε : 0 < ε) : ν {x | ε ≤ |x|} < ⊤ := by
  obtain ⟨h0, hint⟩ := hν
  set a : ℝ := min ε 1 with ha
  have hapos : 0 < a := lt_min hε one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have haε : a ≤ ε := min_le_left _ _
  have hA : MeasurableSet {x : ℝ | a ≤ |x|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have key : ENNReal.ofReal (a ^ 2) * ν {x : ℝ | a ≤ |x|} ≤
      ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
    calc ENNReal.ofReal (a ^ 2) * ν {x : ℝ | a ≤ |x|}
        = ∫⁻ _ in {x : ℝ | a ≤ |x|}, ENNReal.ofReal (a ^ 2) ∂ν := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in {x : ℝ | a ≤ |x|}, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        refine lintegral_mono_ae ((ae_restrict_iff' hA).mpr (Filter.Eventually.of_forall fun x hx => ?_))
        simp only [Set.mem_setOf_eq] at hx
        apply ENNReal.ofReal_le_ofReal
        apply le_min
        · nlinarith
        · have : a ^ 2 ≤ |x| ^ 2 := by gcongr
          rwa [sq_abs] at this
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have h1 : ENNReal.ofReal (a ^ 2) * ν {x : ℝ | a ≤ |x|} < ⊤ :=
    lt_of_le_of_lt key hint
  have h2 : ν {x : ℝ | a ≤ |x|} < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top (by simpa using by positivity)] at h1
    exact lt_irrefl _ h1
  exact lt_of_le_of_lt (measure_mono fun x hx => le_trans haε hx) h2
