-- Prove2me | solution 1 for levy_foundations_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:22:50.477207+00:00
-- url     : https://prove2.me/submissions/9b9bec2d-5202-469f-a688-2e8c56218c6c

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory

theorem solution (ν : Measure ℝ)
    (hν : LevyFoundations.isLevyMeasure ν) : SigmaFinite ν := by
  obtain ⟨h0, hint⟩ := hν
  have hfin : ∀ n : ℕ, ν {x : ℝ | (1 / ((n : ℝ) + 1)) ≤ |x|} < ⊤ := by
    intro n
    set a : ℝ := 1 / ((n : ℝ) + 1) with ha
    have hapos : 0 < a := by positivity
    have ha1 : a ≤ 1 := by
      rw [ha, div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
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
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top (by simpa using by positivity)] at h1
    exact lt_irrefl _ h1
  refine ⟨⟨⟨fun n => {x : ℝ | (1 / ((n : ℝ) + 1)) ≤ |x|} ∪ {0}, fun _ => trivial, ?_, ?_⟩⟩⟩
  · intro n
    refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [h0, add_zero]
    exact hfin n
  · ext x
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    by_cases hx : x = 0
    · exact ⟨0, Or.inr hx⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hx)
      exact ⟨n, Or.inl hn.le⟩
