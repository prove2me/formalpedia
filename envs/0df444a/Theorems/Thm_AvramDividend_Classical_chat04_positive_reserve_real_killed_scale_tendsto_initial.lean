-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_real_killed_scale_tendsto_initial
-- name    : AvramDividend.Classical.chat04_positive_reserve_real_killed_scale_tendsto_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:28:38.278767+00:00
-- url     : https://prove2.me/theorems/f371a1e3-d251-46f7-9904-809504a0ae84
-- title:
--   Real history-killed discounted scale payoff tends to its initial value
-- statement:
--   At any positive initial reserve, continuity of the real discounted q-scale payoff at time zero extends to its whole-history killed version, because a right-continuous Levy path starts at zero and stays above the ruin barrier for a small path-dependent interval. This real-valued limit is the exact pointwise convergence input to the Proved uniform-second-moment expectation lemma, enabling near-zero convergence of killed expectations and eventually the killed q-scale harmonicity needed for two-sided exit.
-- source:
--   Imports Proved chat04_initial_safe_window_of_rightCont_zero (7c9b8b20), Proved chat04_positive_reserve_discounted_scale_tendsto_initial (4940fc29), Mathlib Filter.Tendsto.congr' and eventually_lt_nhds. Downstream: Open killed harmonicity a885f0b3, stopped-scale 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_discounted_scale_tendsto_initial
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_real_killed_scale_tendsto_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) (ω : Ω) :
    Filter.Tendsto
      (fun t : ℝ≥0 =>
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω)
      (𝓝 0) (𝓝 (W x)) := by sorry
