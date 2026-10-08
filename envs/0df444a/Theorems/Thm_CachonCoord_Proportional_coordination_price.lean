-- Prove2me | Theorems.Thm_CachonCoord_Proportional_coordination_price
-- name    : CachonCoord.Proportional.coordination_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:36.858897+00:00
-- url     : https://prove2.me/theorems/7a9ee1c6-ed8c-448f-bca0-b0a99f12316e
-- title:
--   p. 52 — w_b(b) from (20) and (22): q° solves (22) at w_b(b), b < w_b(b) < p, and w_b(b) > ŵ(q°) for b > 0
-- statement:
--   Let $n \ge 2$, $b < p$, let $q^o$ solve (20), and let
--
--   $$
--   w_b(b) = p - (p-b)\left[\frac1n\left(\frac{p-c}{p}\right) + \left(\frac{n-1}{n}\right)\left(\frac1{q^o}\int_0^{q^o}F(x)\,dx\right)\right].
--   $$
--
--   Then
--
--   1. $q^o$ solves (22) for the contract $(w_b(b), b)$: $L_n(q^o) = \dfrac{p - w_b(b)}{p-b}$;
--   2. $b < w_b(b) < p$, so the contract lies in the range where the equilibrium is unique;
--   3. if $b > 0$, then $w_b(b) > \widehat w(q^o)$.
--
--   By the unique-equilibrium theorem, $(w_b(b), b)$ is therefore a coordinating buy-back contract.
--
--   **Formalization Note** $w_b$ is the printed formula, not defined as "the price that coordinates". The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 52 (w_b(b) and "it must be that w_b(b) > ŵ(q°)")

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 52: `w_b(b)`, the wholesale price that coordinates the supply chain given the buy back
rate `b`, is from (20) and (22)
`w_b(b) = p − (p − b) [(1/n)((p − c)/p) + ((n − 1)/n)(1/q°) ∫_0^{q°} F(x) dx]`.
For `b < p`: the integrated optimum `q°` solves (22) at `w = w_b(b)`, the contract satisfies
`b < w_b(b) < p`, and for `b > 0` "it must be that `w_b(b) > ŵ(q°)`". -/
theorem coordination_price (M : Model) (n : ℕ) (hn : 2 ≤ n) (b qo : ℝ) (hb : b < M.p)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    M.lhs22 n qo = (M.p - M.wb n b qo) / (M.p - b) ∧
      b < M.wb n b qo ∧ M.wb n b qo < M.p ∧
      (0 < b → M.what n qo < M.wb n b qo) := by sorry

end CachonCoord.Proportional
