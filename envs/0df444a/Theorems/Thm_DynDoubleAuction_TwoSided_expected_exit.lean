-- Prove2me | Theorems.Thm_DynDoubleAuction_TwoSided_expected_exit
-- name    : DynDoubleAuction.TwoSided.expected_exit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:41.607309+00:00
-- url     : https://prove2.me/theorems/fa64d928-a4f9-4942-9d91-24fac85e21dc
-- title:
--   Proof of Theorem 5.3 — expected number of periods after exit
-- statement:
--   For $T\ge2$ and the initial promise and upper-side condition of Theorem 5.3, the expected number of periods from first entry into an inefficient region through the end of the horizon satisfies
--
--   $$\mathbb E[(T-\tau+1)^+]\le 1+\frac{\underline w_0}{\mu}+\frac{(2\sqrt{8T\log T}+1)\bar v}{\mu}.$$
--
--   This estimate turns the exit tails into a sublinear bound on welfare loss.
--
--   **Formalization Note** Here $\tau$ is the first period $t\in\{1,\dots,T\}$ whose seller promise lies in the low or high region, and $\tau=T+1$ if there is none, so $(T-\tau+1)^+=0$ in that case. The bound is the one printed on p. 30. The cutoff $T^*$ need not be an integer, so the printed chain's step $\sum_{t\le T^*}+T-T^*$ needs slightly finer summation of the two tails, but the printed constant is kept.
-- source:
--   Balseiro, Mirrokni, Paes Leme & Zuo, Dynamic Double Auctions: Towards First Best, SSRN 3213460 (version of November 15, 2018), p. 30, proof of Theorem 5.3

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided

open MeasureTheory Filter Topology

/-- The exit-loss estimate in the proof of Theorem 5.3, with the constant printed on p. 30. -/
theorem expected_exit {n : ℕ} (M : Market n) (hM : Standing M)
    (T : ℕ) (hT : 2 ≤ T)
    (hside : initialPromise M T ≤ wbar M T 1 -
      M.vbar * (1 + Real.sqrt (8 * (T : ℝ) * Real.log T))) :
    (∫ vs, max ((T : ℝ) - (exitTime M T (initialPromise M T) vs : ℝ) + 1) 0
      ∂valueLaw M) ≤
      1 + wlow M / mu M +
        (2 * Real.sqrt (8 * (T : ℝ) * Real.log T) + 1) * M.vbar / mu M := by sorry
end DynDoubleAuction.TwoSided
