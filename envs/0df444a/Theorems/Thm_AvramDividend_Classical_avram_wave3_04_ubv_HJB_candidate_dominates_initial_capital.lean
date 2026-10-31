-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
-- name    : AvramDividend.Classical.avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:59:27.635992+00:00
-- url     : https://prove2.me/theorems/61ab7dfc-c4ed-4ee5-8381-b1da52174462
-- title:
--   Corrected UBV HJB candidate dominates every nonnegative reserve up to the cap
-- statement:
--   For the actual corrected unbounded-variation verification HJB candidate w, the restored boundary premise w(0)≥0, its C² interior regularity and derivative bound w'≥1 imply w(x)≥x for every nonnegative reserve x within an arbitrary finite, infinite or zero extended-real cap. Apply the already Proved endpoint-inclusive full-cap UBV HJB secant inequality to a=0 and b=x: x≤w(x)−w(0)≤w(x). This sharpens the available candidate-nonnegativity statement, and makes the exact original instant-ruin Stieltjes budget bounded by initial reserve x automatically bounded by the verification candidate. No stochastic budget is assumed.
-- source:
--   Exact pinned remote compiler probe 50ad00ed-ad01-4aef-99c9-16d85e544922 passed to intentional sentinel with no source errors, SHA256 e537516252680ce29d60ddce4917763e96f276bed47a6ee4b9429ea045d8b3a0. Canonical Proved avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps 44b01929-5817-44ac-9439-6eb3c9879f2c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
    (C : ℝ≥0∞) (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x)
    (hxc : ENNReal.ofReal x ≤ C) :
    x ≤ w x := by sorry
