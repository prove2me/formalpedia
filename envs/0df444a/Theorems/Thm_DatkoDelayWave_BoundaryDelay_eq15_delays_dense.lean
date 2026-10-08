-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_eq15_delays_dense
-- name    : DatkoDelayWave.BoundaryDelay.eq15_delays_dense
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:59:36.865917+00:00
-- url     : https://prove2.me/theorems/e97e55a3-7b7e-48fe-ada2-56082538b8cc
-- title:
--   Proof of Lemma 2 — the points 2(2m+1)/(2n+1) of (15) are dense in (0, ∞)
-- statement:
--   The set of delays
--   $$
--   \left\{ \frac{2(2m+1)}{2n+1} : m, n \text{ positive integers} \right\}
--   $$
--   is dense in $(0,\infty)$: every positive real number lies in its closure.
--
--   These are the delays of (15) at which the proof of Lemma 2 produces zeros of $f$ in the right half-plane, and the delays at which part (ii) of the THEOREM exhibits spectrum accumulating at the imaginary axis.
--
--   **Formalization Note** As in Lemma 2's proof ((11), (12)), $m$ and $n$ are positive integers.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 154, proof of Lemma 2, sentence after (15)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem eq15_delays_dense :
    Set.Ioi (0 : ℝ) ⊆
      closure {ε : ℝ | ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
            ε = 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1)} := by sorry

end DatkoDelayWave.BoundaryDelay
