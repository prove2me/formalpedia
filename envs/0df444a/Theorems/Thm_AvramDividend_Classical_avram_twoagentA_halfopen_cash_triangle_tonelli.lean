-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_halfopen_cash_triangle_tonelli
-- name    : AvramDividend.Classical.avram_twoagentA_halfopen_cash_triangle_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T09:19:00.001056+00:00
-- url     : https://prove2.me/theorems/1cf140c1-a690-4c33-ab96-196685315cb9
-- title:
--   Half-open original stopped dividend cash triangle Tonelli identity with initial atom
-- statement:
--   For any measure with finite mass on [0,T), Tonelli exchanges the nonnegative integral over {0<=s<T, 0<u<=T, s<u} and yields the exact cumulative mass μ([0,u)) weighted by k(u). This is the triangle identity needed to transport the original right-payment Stieltjes cash with initial atom retained and no terminal payment atom.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_halfopen_cash_triangle_tonelli
    (μ : Measure ℝ) (T : ℝ≥0)
    (hfinite : μ (Ico (0 : ℝ) (T : ℝ)) ≠ ⊤)
    (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ s in Ico (0 : ℝ) (T : ℝ),
      ∫⁻ u in Ioc (0 : ℝ) (T : ℝ),
        if s < u then k u else 0 ∂volume ∂μ) =
    (∫⁻ u in Ioc (0 : ℝ) (T : ℝ),
      k u * μ (Ico (0 : ℝ) u) ∂volume) := by sorry
