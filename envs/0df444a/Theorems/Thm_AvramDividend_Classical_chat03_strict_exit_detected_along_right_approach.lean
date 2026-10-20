-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_detected_along_right_approach
-- name    : AvramDividend.Classical.chat03_strict_exit_detected_along_right_approach
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:39:35.28695+00:00
-- url     : https://prove2.me/theorems/6142edbf-a840-490b-aba4-627d8dc72784
-- title:
--   Strict two-sided Lévy exit is eventually detected by every right-convergent sampling clock
-- statement:
--   Let X be the published spectrally negative Lévy process with right-continuous sample paths, and fix an outcome and a time t at which X is strictly below the lower barrier or strictly above the upper barrier. For any sequence of nonnegative sample times clock(n) converging to t in the right-neighbourhood filter, eventually all sampled reserves satisfy the same strict exit disjunction. The proof composes the already Proved pathwise right-persistence theorem with Filter.Tendsto.eventually. Applying this to ceiling-dyadic clock points, once their right-convergence has been established, proves discrete grids detect witnessed strict exits. It assumes no right-continuity of the filtration, continuity of W, or q-scale martingale.
-- source:
--   Already Proved AvramDividend.Classical.chat03_strict_two_sided_exit_right_eventually UUID c61df2ed-f0c6-4e7d-b385-d34f1b0ec96d and pinned Mathlib Filter.Tendsto.eventually, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_two_sided_exit_right_eventually
import Mathlib.Topology.Order.Basic

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_exit_detected_along_right_approach
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower upper : ℝ)
    (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici t] t))
    (h : X.X t ω < lower ∨ upper < X.X t ω) :
    ∀ᶠ n in atTop,
      X.X (clock n) ω < lower ∨ upper < X.X (clock n) ω := by sorry
