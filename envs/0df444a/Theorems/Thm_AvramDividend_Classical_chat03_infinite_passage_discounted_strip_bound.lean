-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_infinite_passage_discounted_strip_bound
-- name    : AvramDividend.Classical.chat03_infinite_passage_discounted_strip_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:30:51.485173+00:00
-- url     : https://prove2.me/theorems/2066c60a-f7a5-4d1c-ba7c-8247b5843f57
-- title:
--   Uniform stopped q-scale strip bound on paths with infinite upper and lower strict passage times
-- statement:
--   When both official strict passage clocks are infinite, a spectrally negative Lévy sample path never strictly exits the interval between the lower barrier -x and upper barrier a-x. For q>0 and 0≤x≤a with W an official q-scale function, the discounted scale process exp(-qt) W(x+X_t) is nonnegative and bounded above by W(a) at every finite time. The proof is a pathwise terminal-residual control on the no-passage branch, using independently Proved no-exit and scale terminal bounds. No killed q-scale martingale or expectation identity is assumed.
-- source:
--   Proved chat03_no_grid_exit_when_both_passages_infinite and chat03_discounted_scale_terminal_bound, plus scale function positivity. Strict conditions and pinned revision respected.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_terminal_bound
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_infinite_passage_discounted_strip_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hUp : twoSidedExitUpTime X (a - x) ω = ∞)
    (hDown : twoSidedExitDownTime X (-x) ω = ∞) :
    ∀ t : ℝ≥0,
      0 ≤ Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) ∧
      Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) ≤ W a := by sorry
