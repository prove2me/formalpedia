-- Prove2me | Theorems.Thm_CrowdTarget_Separating_profit_closed_form
-- name    : CrowdTarget.Separating.profit_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:01.196565+00:00
-- url     : https://prove2.me/theorems/635c0ab9-d82b-403c-af6c-77acc2ccc152
-- title:
--   Closed form of the expected profit (1)
-- statement:
--   Let a share $k>0$ of the $N\sim U[0,\bar N]$ backers pledge at price $p>0$ to a campaign with target $C$ and startup cost $S$.
--
--   1. If $0\le C<kp\bar N$, then
--   $$
--   \Pi=\frac{\bar N}{2}\,kp+\frac{2SC-C^2}{2\bar N\,kp}-S .
--   $$
--   2. If $C>0$ and $kp\bar N\le C$ (for any $k$, $p$), then $\Pi=0$: the campaign cannot succeed.
--
--   With $k=1$ this is the complete-information profit of the proof of Proposition 1; with $k=1-\alpha$ it is the informed-only deviation profit, Online Supplement (4); with $k=\alpha$ it is the mimicking profit, Online Supplement (5).
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 1, proof of Proposition 1 (also Online Supplement (4), p. 3, and (5), p. 4)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 1, proof of Proposition 1: the closed form of (1).

With a share `k > 0` of the backers pledging at price `p > 0`, a target `0 ≤ C < k p N̄` and
startup cost `S`, the expected profit is `(N̄/2)(kp) + (2SC − C²)/(2N̄ kp) − S`; for a positive
target `C ≥ k p N̄` it is `0`. With `k = 1` this is the supplement's complete-information formula,
with `k = 1 − α` it is Online Supplement (4) (p. 3), with `k = α` Online Supplement (5) (p. 4). -/
theorem profit_closed_form (P : Params) (hP : P.Standing) (k S C p : ℝ) :
    (0 < k → 0 < p → 0 ≤ C → C < k * p * P.Nbar →
      campaignProfit P k S C p =
        P.Nbar / 2 * (k * p) + (2 * S * C - C ^ 2) / (2 * P.Nbar * (k * p)) - S) ∧
    (0 < C → k * p * P.Nbar ≤ C → campaignProfit P k S C p = 0) := by sorry

end CrowdTarget.Separating
