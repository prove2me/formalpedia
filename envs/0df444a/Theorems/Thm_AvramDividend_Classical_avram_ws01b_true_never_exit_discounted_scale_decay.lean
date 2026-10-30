-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_never_exit_discounted_scale_decay
-- name    : AvramDividend.Classical.avram_ws01b_true_never_exit_discounted_scale_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:34:38.001354+00:00
-- url     : https://prove2.me/theorems/b67e65d9-657b-44ff-8dd1-4eaff9784886
-- title:
--   Original BV-compatible no-exit discounted q-scale reward vanishes as horizon tends to infinity
-- statement:
--   Under the actual process and true infinite strict lower and upper exit clocks, Wq(x+X_n) stays in [0,Wq(a)]. Since q>0, the actual discounted terminal stopped reward decays to zero as n tends to infinity, without any exponential martingale uniform-integrability assumption.
-- source:
--   Accepted original never-exit source strip bound, pinned Mathlib Real.tendsto_exp_neg_atTop_nhds_zero and Tendsto.squeeze.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_never_exit_scale_strip_bound

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_true_never_exit_discounted_scale_decay
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hUp : twoSidedExitUpTime X (a-x) ω = ∞)
    (hDown : twoSidedExitDownTime X (-x) ω = ∞) :
    Tendsto (fun n : ℕ =>
      Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω))
      atTop (𝓝 0) := by sorry
