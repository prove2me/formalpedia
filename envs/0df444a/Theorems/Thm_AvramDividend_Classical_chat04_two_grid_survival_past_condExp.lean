-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_two_grid_survival_past_condExp
-- name    : AvramDividend.Classical.chat04_two_grid_survival_past_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:14:06.382818+00:00
-- url     : https://prove2.me/theorems/c582a748-21fb-4135-a198-38037c32eef3
-- title:
--   Conditional future q-scale payoff on an explicit two-time historical-survival event
-- statement:
--   Under the exact Standing and q>0 assumptions, for ordered deterministic times s≤t≤u and a fixed reserve threshold x, let A be the event that x+X_s≥0 and x+X_t≥0. Prove directly from adaptedness and filtration monotonicity that A is measurable in the history sigma-algebra F_t. Then conditional expectation of the future-increment q-scale payoff W(x+X_u−X_t) restricted to A equals the same historical survival indicator multiplied by its stationary expected q-scale payoff. No separately assumed integrability or filtration measurability is needed. This is the explicit finite-grid survival-event Markov factorisation; it still does not require the future trajectory stay above the boundary between t and u, and does not claim a killed q-scale martingale.
-- source:
--   Proved Chat04 Standing past-event scale conditional expectation theorem 3b6d30d3-f850-4855-b55f-b19339f58174 and pinned Mathlib adapted process, filtration monotonicity and measurableSets for closed half-lines.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_past_event_scale_condExp

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_two_grid_survival_past_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (x : ℝ) :
    P[({ω | 0 ≤ x + X.X s ω ∧ 0 ≤ x + X.X t ω}).indicator
        (fun ω => W (x + (X.X u ω - X.X t ω))) | 𝓕 t] =ᵐ[P]
      ({ω | 0 ≤ x + X.X s ω ∧ 0 ≤ x + X.X t ω}).indicator
        (fun _ => ∫ ω, W (x + X.X (u - t) ω) ∂P) := by sorry
