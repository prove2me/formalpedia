-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEquilibrium_seller_best_response
-- name    : ChatterjeeSamuelson.UniformEquilibrium.seller_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:07:51.682684+00:00
-- url     : https://prove2.me/theorems/efe7be89-03ef-4877-8061-c19129858d5f
-- title:
--   Example 1(a), seller half — the seller's strategy is a best response
-- statement:
--   Let $0 \le k \le 1$ and $\bar v > 0$, let both reservation prices lie in $[0, \bar v]$, and let each player's belief about the other's value be uniform on $[0, \bar v]$. Let $S, B : \mathbb R \to \mathbb R$ be measurable offer strategies such that
--
--   1. $S(v_s) = \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $0 \le v_s \le \frac{2-k}{2}\bar v$;
--   2. $S(v_s) \ge \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $\frac{2-k}{2}\bar v < v_s \le \bar v$;
--   3. $B(v_b) \le \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $0 \le v_b < \frac{1-k}{2}\bar v$;
--   4. $B(v_b) = \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $\frac{1-k}{2}\bar v \le v_b \le \bar v$.
--
--   Then for every seller value $v \in [0, \bar v]$ and every real ask $s$,
--
--   $$
--   \pi_s(s, v) \le \pi_s(S(v), v),
--   $$
--
--   where $\pi_s$ is the seller's expected profit against $B$ under the uniform belief. That is, $S$ is a best response to $B$ for every seller type.
--
--   Together with the buyer half, this is the statement that $(S, B)$ is an equilibrium (Example 1(a)).
--
--   **Formalization Note** Measurability of $S$ and $B$ is added: the page leaves $S$ on the upper range and $B$ on the lower range free up to an inequality, and a non-measurable choice would make expected profits meaningless. The printed coefficient $(k(1-k)/2(1+k))\bar v$ is read as $\frac{k(1-k)}{2(1+k)}\bar v$.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), https://doi.org/10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(a) (seller's best-response half)

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_unif
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.UniformEquilibrium

/-- Example 1(a), seller half (Chatterjee & Samuelson, *Bargaining under Incomplete
Information*, Oper. Res. 31(5) 1983, §3, Example 1(a), p. 842 [PDF 8]): with both values
uniform on `[0, v̄]` (`F_s(v) = F_b(v) = v/v̄`), the seller's strategy `S` of Example 1(a) is a
best response to the buyer's strategy `B` of Example 1(a): for every seller value
`v ∈ [0, v̄]` and every real ask `s`, `π_s(s, v) ≤ π_s(S(v), v)`, where the seller's belief
about the buyer's value is uniform on `[0, v̄]`.

Hypotheses: `0 ≤ k ≤ 1`, `0 < v̄`, `S` and `B` measurable, and the four lines of
Example 1(a) on their printed ranges:
1. `S v = v/(2 − k) + ((1 − k)/2) v̄` for `0 ≤ v ≤ ((2 − k)/2) v̄`;
2. `S v ≥ v/(2 − k) + ((1 − k)/2) v̄` for `((2 − k)/2) v̄ < v ≤ v̄`;
3. `B v ≤ v/(1 + k) + (k(1 − k)/(2(1 + k))) v̄` for `0 ≤ v < ((1 − k)/2) v̄`;
4. `B v = v/(1 + k) + (k(1 − k)/(2(1 + k))) v̄` for `((1 − k)/2) v̄ ≤ v ≤ v̄`.
`S`, `B` are unconstrained outside `[0, v̄]`.

*Formalization Note.*
`Measurable S`, `Measurable B` are added: the page leaves `S` above
`((2 − k)/2) v̄` and `B` below `((1 − k)/2) v̄` free up to an inequality, and a
non-measurable choice would make an expected profit a junk Bochner integral; the paper's
offer densities `g_b`, `g_s` presuppose measurable strategies. The printed coefficient `k(1 − k)/2(1 + k)` is read as
`k(1 − k)/(2(1 + k))` (see `buyerLinear`). -/
theorem seller_best_response (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar)
    (S B : ℝ → ℝ) (hSmeas : Measurable S) (hBmeas : Measurable B)
    (hS_eq : ∀ v, 0 ≤ v → v ≤ (2 - k) / 2 * vbar → S v = Shared.sellerLinear k vbar v)
    (hS_ge : ∀ v, (2 - k) / 2 * vbar < v → v ≤ vbar → Shared.sellerLinear k vbar v ≤ S v)
    (hB_le : ∀ v, 0 ≤ v → v < (1 - k) / 2 * vbar → B v ≤ Shared.buyerLinear k vbar v)
    (hB_eq : ∀ v, (1 - k) / 2 * vbar ≤ v → v ≤ vbar → B v = Shared.buyerLinear k vbar v) :
    ∀ v ∈ Icc (0 : ℝ) vbar, ∀ s : ℝ,
      Shared.sellerProfit k (Shared.unif vbar) B s v ≤ Shared.sellerProfit k (Shared.unif vbar) B (S v) v := by sorry

end ChatterjeeSamuelson.UniformEquilibrium
