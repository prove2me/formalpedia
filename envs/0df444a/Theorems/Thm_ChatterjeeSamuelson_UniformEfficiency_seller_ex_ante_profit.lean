-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEfficiency_seller_ex_ante_profit
-- name    : ChatterjeeSamuelson.UniformEfficiency.seller_ex_ante_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T08:47:51.744977+00:00
-- url     : https://prove2.me/theorems/85975e4f-1c4e-4fc8-86df-c3b00e5482c4
-- title:
--   Example 1(c)(i): the seller's expected profit is $(\bar v/48)(2-k)^2(1+k)$, strictly decreasing in $k$
-- statement:
--   Let $0 \le k \le 1$ and $\bar v > 0$, let the reservation prices $v_s$, $v_b$ be independent and uniform on $[0, \bar v]$, and let the offer strategies $S$, $B$ have the shape of Example 1(a) (seller: $S(v_s) = \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $v_s \le \frac{2-k}{2}\bar v$ and at least that above; buyer: $B(v_b) = \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $v_b \ge \frac{1-k}{2}\bar v$ and at most that below).
--
--   Then the seller's ex ante expected profit under the sealed-offer rule with price $kb + (1-k)s$ is
--
--   $$
--   \pi_s(k) = \frac{\bar v}{48}\,(2-k)^2(1+k),
--   $$
--
--   and $k \mapsto \frac{\bar v}{48}(2-k)^2(1+k)$ is strictly decreasing on $[0,1]$.
--
--   Raising $k$ moves the price toward the buyer's offer, yet the seller's equilibrium profit falls, because both strategies adjust to the rule.
--
--   **Formalization Note** Monotonicity is over $k \in [0,1]$; the cubic is not monotone on all of $\mathbb R$. The equilibrium property of $S, B$ is not assumed.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(c)(i); p. 843 [PDF 9] ("ex ante profit")

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_sellerExAnte

open Set

namespace ChatterjeeSamuelson.UniformEfficiency

/-- Example 1(c)(i) (Chatterjee & Samuelson, *Bargaining under Incomplete Information*, Oper.
Res. 31(5) 1983, §3, Example 1(c)(i), p. 842 [PDF 8]: "The seller's expected profit is
π_s(k) = (v̄/48)(2 − k)²(1 + k) which is strictly decreasing in k."; p. 843 [PDF 9]: "part c
describes each player's ex ante profit").

Let `0 ≤ k ≤ 1`, `0 < v̄`, and let `S`, `B` be offer strategies of the shape of Example 1(a).
With `(v_s, v_b)` independent and uniform on `[0, v̄]`, the seller's ex ante expected profit is
`(v̄/48)(2 − k)²(1 + k)`, and `κ ↦ (v̄/48)(2 − κ)²(1 + κ)` is strictly decreasing on `[0, 1]`.

*Formalization Note.* Monotonicity is over the rule parameter on `[0, 1]` (the cubic is not
monotone on all of `ℝ`). The equilibrium property of `S, B` is not assumed. -/
theorem seller_ex_ante_profit (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar)
    (S B : ℝ → ℝ) (hSB : IsExample1Pair k vbar S B) :
    sellerExAnte k vbar S B = vbar / 48 * (2 - k) ^ 2 * (1 + k) ∧
      StrictAntiOn (fun κ : ℝ => vbar / 48 * (2 - κ) ^ 2 * (1 + κ)) (Icc 0 1) := by sorry

end ChatterjeeSamuelson.UniformEfficiency
