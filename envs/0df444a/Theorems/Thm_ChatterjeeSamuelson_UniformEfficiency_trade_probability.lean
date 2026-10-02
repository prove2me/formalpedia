-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEfficiency_trade_probability
-- name    : ChatterjeeSamuelson.UniformEfficiency.trade_probability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T08:37:57.686261+00:00
-- url     : https://prove2.me/theorems/337bf25d-d734-4224-a2da-4bb365ad753b
-- title:
--   Example 1(b): a bargain is reached with probability $(-k^2+k+2)/8$, at most $9/32$
-- statement:
--   Let $0 \le k \le 1$ and $\bar v > 0$. Suppose the reservation prices $v_s$ and $v_b$ are independent and uniform on $[0, \bar v]$, and the seller and buyer use offer strategies $S$, $B$ of the shape of Example 1(a):
--
--   1. $S(v_s) = \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $0 \le v_s \le \frac{2-k}{2}\bar v$, and $S(v_s)$ is at least this for $\frac{2-k}{2}\bar v < v_s \le \bar v$;
--   2. $B(v_b) = \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $\frac{1-k}{2}\bar v \le v_b \le \bar v$, and $B(v_b)$ is at most this for $0 \le v_b < \frac{1-k}{2}\bar v$.
--
--   Then the probability that a bargain is reached is
--
--   $$
--   \Pr\bigl[S(v_s) \le B(v_b)\bigr] = \frac{-k^2 + k + 2}{8},
--   $$
--
--   and, as a function of the rule parameter $k \in [0,1]$, this probability attains its maximum value $9/32$ at $k = 1/2$.
--
--   The trade region computed here is the domain of integration of both players' expected profits in Example 1(c). The probability does not depend on $\bar v$.
--
--   **Formalization Note** The maximum is stated as `IsMaxOn` of $\kappa \mapsto (-\kappa^2+\kappa+2)/8$ on $[0,1]$ at $1/2$, together with the value $9/32$. The equilibrium property of $S, B$ is not assumed.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(b)

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_tradeProb

open Set

namespace ChatterjeeSamuelson.UniformEfficiency

/-- Example 1(b) (Chatterjee & Samuelson, *Bargaining under Incomplete Information*, Oper.
Res. 31(5) 1983, §3, Example 1(b), p. 842 [PDF 8]: "The probability that a bargain is reached
equals (−k² + k + 2)/8 and achieves it maximum value, 9/32, at k = ½.").

Let `0 ≤ k ≤ 1`, `0 < v̄`, and let `S`, `B` be offer strategies of the shape of Example 1(a)
(`IsExample1Pair k v̄ S B`). With the reservation prices `(v_s, v_b)` independent and uniform
on `[0, v̄]`, the probability that `S(v_s) ≤ B(v_b)` is `(−k² + k + 2)/8`; moreover the map
`κ ↦ (−κ² + κ + 2)/8` attains its maximum over `κ ∈ [0, 1]` at `κ = 1/2`, where it equals
`9/32`.

*Formalization Note.* The maximum is over the rule parameter `k ∈ [0, 1]` of the Bargaining
Rule (p. 838). The equilibrium property of `S, B` is not assumed: the computation uses only the
shape of the strategies. -/
theorem trade_probability (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar)
    (S B : ℝ → ℝ) (hSB : IsExample1Pair k vbar S B) :
    tradeProb vbar S B = (-k ^ 2 + k + 2) / 8 ∧
      IsMaxOn (fun κ : ℝ => (-κ ^ 2 + κ + 2) / 8) (Icc 0 1) (1 / 2) ∧
      (-(1 / 2 : ℝ) ^ 2 + 1 / 2 + 2) / 8 = 9 / 32 := by sorry

end ChatterjeeSamuelson.UniformEfficiency
