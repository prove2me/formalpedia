-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEfficiency_buyer_ex_ante_profit
-- name    : ChatterjeeSamuelson.UniformEfficiency.buyer_ex_ante_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T08:58:13.915003+00:00
-- url     : https://prove2.me/theorems/a1792fec-e182-4cf3-accb-785ad72a4329
-- title:
--   Example 1(c)(ii): the buyer's expected profit is $(\bar v/48)(1+k)^2(2-k)$, strictly increasing in $k$
-- statement:
--   Let $0 \le k \le 1$ and $\bar v > 0$, let the reservation prices $v_s$, $v_b$ be independent and uniform on $[0, \bar v]$, and let the offer strategies $S$, $B$ have the shape of Example 1(a) (seller: $S(v_s) = \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $v_s \le \frac{2-k}{2}\bar v$ and at least that above; buyer: $B(v_b) = \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $v_b \ge \frac{1-k}{2}\bar v$ and at most that below).
--
--   Then the buyer's ex ante expected profit under the sealed-offer rule with price $kb + (1-k)s$ is
--
--   $$
--   \pi_b(k) = \frac{\bar v}{48}\,(1+k)^2(2-k),
--   $$
--
--   and $k \mapsto \frac{\bar v}{48}(1+k)^2(2-k)$ is strictly increasing on $[0,1]$.
--
--   Giving the buyer's offer more weight in the price benefits the buyer once both strategies adjust to the rule.
--
--   **Formalization Note** Monotonicity is over $k \in [0,1]$; the cubic is not monotone on all of $\mathbb R$. The equilibrium property of $S, B$ is not assumed.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(c)(ii); p. 843 [PDF 9] ("ex ante profit")

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_buyerExAnte

open Set

namespace ChatterjeeSamuelson.UniformEfficiency

/-- Example 1(c)(ii) (Chatterjee & Samuelson, *Bargaining under Incomplete Information*, Oper.
Res. 31(5) 1983, §3, Example 1(c)(ii), p. 842 [PDF 8]: "The buyer's expected profit is
π_b(k) = (v̄/48)(1 + k)²(2 − k) which is strictly increasing in k."; p. 843 [PDF 9]: "part c
describes each player's ex ante profit").

Let `0 ≤ k ≤ 1`, `0 < v̄`, and let `S`, `B` be offer strategies of the shape of Example 1(a).
With `(v_s, v_b)` independent and uniform on `[0, v̄]`, the buyer's ex ante expected profit is
`(v̄/48)(1 + k)²(2 − k)`, and `κ ↦ (v̄/48)(1 + κ)²(2 − κ)` is strictly increasing on `[0, 1]`.

*Formalization Note.* Monotonicity is over the rule parameter on `[0, 1]` (the cubic is not
monotone on all of `ℝ`). The equilibrium property of `S, B` is not assumed. -/
theorem buyer_ex_ante_profit (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar)
    (S B : ℝ → ℝ) (hSB : IsExample1Pair k vbar S B) :
    buyerExAnte k vbar S B = vbar / 48 * (1 + k) ^ 2 * (2 - k) ∧
      StrictMonoOn (fun κ : ℝ => vbar / 48 * (1 + κ) ^ 2 * (2 - κ)) (Icc 0 1) := by sorry

end ChatterjeeSamuelson.UniformEfficiency
