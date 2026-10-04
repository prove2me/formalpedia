-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEfficiency_total_profit
-- name    : ChatterjeeSamuelson.UniformEfficiency.total_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:12:01.289084+00:00
-- url     : https://prove2.me/theorems/44b8dbaa-a1fe-4ac8-a8d1-308316ba0cda
-- title:
--   Example 1(c)(iii): total expected profit $(\bar v/16)(1+k)(2-k)$, maximal $(9/64)\bar v$ at $k = 1/2$
-- statement:
--   Let $0 \le k \le 1$ and $\bar v > 0$. Suppose the reservation prices $v_s$ and $v_b$ are independent and uniform on $[0, \bar v]$, and the seller and buyer use offer strategies $S$, $B$ of the shape of Example 1(a):
--
--   1. $S(v_s) = \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $0 \le v_s \le \frac{2-k}{2}\bar v$, and $S(v_s)$ is at least this for $\frac{2-k}{2}\bar v < v_s \le \bar v$;
--   2. $B(v_b) = \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $\frac{1-k}{2}\bar v \le v_b \le \bar v$, and $B(v_b)$ is at most this for $0 \le v_b < \frac{1-k}{2}\bar v$.
--
--   Under the sealed-offer rule (trade iff $B(v_b) \ge S(v_s)$, at price $kB(v_b) + (1-k)S(v_s)$), the sum of the seller's and the buyer's ex ante expected profits is
--
--   $$
--   \pi_s + \pi_b = \frac{\bar v}{16}\,(1+k)(2-k),
--   $$
--
--   and, as a function of the rule parameter $k \in [0,1]$, this total attains its maximum $\frac{9}{64}\bar v$ at $k = 1/2$.
--
--   The split-the-difference rule $k = 1/2$ thus maximizes expected group profit among these equilibria of the sealed-offer rule for uniform values.
--
--   **Formalization Note** The maximum is stated as `IsMaxOn` of $\kappa \mapsto \frac{\bar v}{16}(1+\kappa)(2-\kappa)$ on $[0,1]$ at $1/2$, together with the value $\frac{9}{64}\bar v$. The equilibrium property of $S, B$ is not assumed: the result is a computation about any strategies of this shape.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(c)(iii); p. 843 [PDF 9] ("ex ante profit")

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_sellerExAnte
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_buyerExAnte

open Set

namespace ChatterjeeSamuelson.UniformEfficiency

/-- Example 1(c)(iii) (Chatterjee & Samuelson, *Bargaining under Incomplete Information*, Oper.
Res. 31(5) 1983, §3, Example 1(c)(iii), p. 842 [PDF 8]: "The sum of the parties' profits is
π_s + π_b = (v̄/16)(1 + k)(2 − k), which has a maximum of (9/64)v̄, at k = ½."; p. 843 [PDF 9]:
"part c describes each player's ex ante profit").

Let `0 ≤ k ≤ 1`, `0 < v̄`, and let `S`, `B` be offer strategies of the shape of Example 1(a)
(`IsExample1Pair k v̄ S B`). With `(v_s, v_b)` independent and uniform on `[0, v̄]`, the sum of
the seller's and the buyer's ex ante expected profits is `(v̄/16)(1 + k)(2 − k)`; moreover the
map `κ ↦ (v̄/16)(1 + κ)(2 − κ)` attains its maximum over `κ ∈ [0, 1]` at `κ = 1/2`, where it
equals `(9/64)v̄`.

*Formalization Note.* The maximum is over the rule parameter `k ∈ [0, 1]` of the Bargaining
Rule (p. 838). The equilibrium property of `S, B` is not assumed: the computation uses only the
shape of the strategies. -/
theorem total_profit (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar)
    (S B : ℝ → ℝ) (hSB : IsExample1Pair k vbar S B) :
    sellerExAnte k vbar S B + buyerExAnte k vbar S B = vbar / 16 * (1 + k) * (2 - k) ∧
      IsMaxOn (fun κ : ℝ => vbar / 16 * (1 + κ) * (2 - κ)) (Icc 0 1) (1 / 2) ∧
      vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2) = 9 / 64 * vbar := by sorry

end ChatterjeeSamuelson.UniformEfficiency
