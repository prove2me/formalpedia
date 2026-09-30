-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEquilibrium_linear_equilibrium
-- name    : ChatterjeeSamuelson.UniformEquilibrium.linear_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:09:05.870829+00:00
-- url     : https://prove2.me/theorems/5c718845-70b1-4649-abc0-cfeb6a3bd5ca
-- title:
--   Example 1(a) — the linear equilibrium of the sealed-offer rule for uniform values
-- statement:
--   Consider the sealed-offer bargaining game in which the seller asks $s$, the buyer offers $b$, and trade occurs iff $b \ge s$ at price $kb + (1-k)s$. Let $0 \le k \le 1$ and $\bar v > 0$, let both reservation prices lie in $[0, \bar v]$, and let each player's belief about the other's value be uniform on $[0, \bar v]$, i.e. $F_s(v) = F_b(v) = v/\bar v$.
--
--   Let $S, B : \mathbb R \to \mathbb R$ be measurable offer strategies such that
--
--   1. $S(v_s) = \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $0 \le v_s \le \frac{2-k}{2}\bar v$;
--   2. $S(v_s) \ge \frac{v_s}{2-k} + \frac{1-k}{2}\bar v$ for $\frac{2-k}{2}\bar v < v_s \le \bar v$;
--   3. $B(v_b) \le \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $0 \le v_b < \frac{1-k}{2}\bar v$;
--   4. $B(v_b) = \frac{v_b}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$ for $\frac{1-k}{2}\bar v \le v_b \le \bar v$.
--
--   Then $(S, B)$ is a Bayesian (Nash) equilibrium: for every buyer value $v \in [0, \bar v]$ and every real $b$, $\pi_b(b, v) \le \pi_b(B(v), v)$, and for every seller value $v \in [0, \bar v]$ and every real $s$, $\pi_s(s, v) \le \pi_s(S(v), v)$.
--
--   This is the linear equilibrium of the $k$-double auction with uniform values, the standard worked example of bilateral trade under two-sided private information; at $k = 1/2$ it attains the Myerson–Satterthwaite second-best bound.
--
--   **Formalization Note** Only sufficiency is stated: every pair satisfying the four conditions is an equilibrium. The paper does not claim that every equilibrium has this form (p. 842 notes other equilibria exist). Measurability of $S$ and $B$ is added; the paper's offer densities presuppose it. The printed coefficient $(k(1-k)/2(1+k))\bar v$ is read as $\frac{k(1-k)}{2(1+k)}\bar v$. Values of $S$, $B$ outside $[0, \bar v]$ are unconstrained and irrelevant.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), https://doi.org/10.1287/opre.31.5.835, p. 842 [PDF 8], §3 Example 1(a)

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_unif
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.UniformEquilibrium

/-- Example 1(a) (Chatterjee & Samuelson, *Bargaining under Incomplete Information*,
Oper. Res. 31(5) 1983, §3, Example 1(a), p. 842 [PDF 8]): "Suppose the parties bargain
under the sealed offer rule with F_s(v) = F_b(v) = v/v̄. […] The equilibrium offer
strategies, S( ) and B( ), are given by" the four lines below. Every pair `(S, B)` satisfying
them is a Nash (Bayesian) equilibrium of the sealed-offer game in which both values lie in
`[0, v̄]` and each player's belief about the other's value is uniform on `[0, v̄]`.

Hypotheses: `0 ≤ k ≤ 1`, `0 < v̄`, `S` and `B` measurable, and the four lines of
Example 1(a) on their printed ranges:
1. `S v = v/(2 − k) + ((1 − k)/2) v̄` for `0 ≤ v ≤ ((2 − k)/2) v̄`;
2. `S v ≥ v/(2 − k) + ((1 − k)/2) v̄` for `((2 − k)/2) v̄ < v ≤ v̄`;
3. `B v ≤ v/(1 + k) + (k(1 − k)/(2(1 + k))) v̄` for `0 ≤ v < ((1 − k)/2) v̄`;
4. `B v = v/(1 + k) + (k(1 − k)/(2(1 + k))) v̄` for `((1 − k)/2) v̄ ≤ v ≤ v̄`.
`S`, `B` are unconstrained outside `[0, v̄]`.

*Formalization Note.* Only the sufficiency direction is stated: the paper does not claim,
and §3 (p. 842) explicitly denies, that every equilibrium has this form.
`Measurable S`, `Measurable B` are added: the page leaves `S` above
`((2 − k)/2) v̄` and `B` below `((1 − k)/2) v̄` free up to an inequality, and a
non-measurable choice would make an expected profit a junk Bochner integral; the paper's
offer densities `g_b`, `g_s` presuppose measurable strategies. The
printed coefficient `k(1 − k)/2(1 + k)` is read as `k(1 − k)/(2(1 + k))` (see
`buyerLinear`). Deviations range over all real offers (see `IsEquilibrium`). -/
theorem linear_equilibrium (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar)
    (S B : ℝ → ℝ) (hSmeas : Measurable S) (hBmeas : Measurable B)
    (hS_eq : ∀ v, 0 ≤ v → v ≤ (2 - k) / 2 * vbar → S v = Shared.sellerLinear k vbar v)
    (hS_ge : ∀ v, (2 - k) / 2 * vbar < v → v ≤ vbar → Shared.sellerLinear k vbar v ≤ S v)
    (hB_le : ∀ v, 0 ≤ v → v < (1 - k) / 2 * vbar → B v ≤ Shared.buyerLinear k vbar v)
    (hB_eq : ∀ v, (1 - k) / 2 * vbar ≤ v → v ≤ vbar → B v = Shared.buyerLinear k vbar v) :
    Shared.IsEquilibrium k (Shared.unif vbar) (Shared.unif vbar) 0 vbar 0 vbar S B := by sorry

end ChatterjeeSamuelson.UniformEquilibrium
