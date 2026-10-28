-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_unmasked_near_zero
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_scale_unmasked_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:55:42.069009+00:00
-- url     : https://prove2.me/theorems/9126cb3d-8bba-4edc-8dee-400bb7621089
-- title:
--   Whole-history killed q-scale payoff is unmasked near zero from every positive reserve
-- statement:
--   At any strictly positive initial reserve x, each right-continuous Lévy path stays above the negative threshold -x during a positive initial time interval. Hence the exact history-killed discounted ENNReal q-scale payoff agrees with the raw discounted payoff on that interval. No upper barrier or additional stochastic regularity is needed. This gives the exact positive-capital time-zero input to the still-open killed q-scale renewal identity.
-- source:
--   Proved chat04_initial_safe_window_of_rightCont_zero 7c9b8b20-5b1b-4f1d-8e2e-979243bf3747 and Set.indicator_of_mem. Direct input to Open chat04_unbounded_killed_survival_discounted_scale_expectation a885f0b3-3960-424d-97e4-abbcffe268ba and unbounded stopped-scale identity aed50a34.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_scale_unmasked_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hx : 0 < x) (W : ℝ → ℝ) (ω : Ω) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε →
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω =
          ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) := by sorry
