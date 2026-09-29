-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_LinkedODE_buyer_first_order_condition
-- name    : ChatterjeeSamuelson.LinkedODE.buyer_first_order_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:47:20.503573+00:00
-- url     : https://prove2.me/theorems/f5a28f41-d60e-4a3b-87bb-5caac776b040
-- title:
--   Proof of Theorem 2: the buyer's first-order condition
-- statement:
--   Let $0 \le k \le 1$. Let the buyer's belief $\mu_b$ about the seller's value be a regular belief on $[\underline v_s, \bar v_s]$ with distribution function $F_b$ and density $f_b$, and let the seller's strategy $S$ be of class $A$ on $[\underline v_s, \bar v_s]$. Let $y$ lie in an open interval $(a, c) \subseteq [\underline v_s, \bar v_s]$ on which $S$ is strictly increasing, and suppose $S'(y) > 0$. Then:
--
--   1. for every reservation price $v$, the buyer's expected profit $b \mapsto \pi_b(b, v)$ is differentiable at $b = S(y)$, with
--   $$
--   \frac{\partial \pi_b}{\partial b}(S(y), v) = \bigl(v - S(y)\bigr)\frac{f_b(y)}{S'(y)} - k F_b(y);
--   $$
--   2. if $(S, B)$ is an equilibrium, then for every buyer value $x \in [\underline v_b, \bar v_b]$ with $B(x) = S(y)$,
--   $$
--   \bigl(x - S(y)\bigr)\frac{f_b(y)}{S'(y)} - k F_b(y) = 0.
--   $$
--
--   This is the paper's first-order condition $(v_b - b) g_b(b) - k G_b(b) = 0$ with $g_b(b) = f_b(y)/S'(y)$ and $G_b(b) = F_b(y)$ at $b = S(y)$; rearranged, it is equation (3a).
--
--   **Formalization Note** The hypothesis $S'(y) > 0$ is not stated in the paper; it is what makes the offer density $f_b(y)/S'(y)$ finite. The buyer value $x$ with $B(x) = S(y)$ is the paper's $B^{-1}(S(y))$.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 840 [PDF 6], proof of Theorem 2, display "∂π_b/∂b = (v_b − b)g_b(b) − kG_b(b) = 0"

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- The buyer's first-order condition (Chatterjee & Samuelson, *Bargaining under
Incomplete Information*, Oper. Res. 31(5) 1983, §2, p. 840 [PDF 6], proof of Theorem 2,
unnumbered display "∂π_b/∂b = (v_b − b)g_b(b) − kG_b(b) = 0", together with
"g_b(b) = f_b(y)/S′(y)" and "G_b(b) = F_b(y)" for `b = S(y)`).

Let `0 ≤ k ≤ 1`, let the buyer's belief `μb` about the seller's value be regular on
`[loS, hiS]` with density `fb`, let `S` be of class `A` on `[loS, hiS]`, let `y` lie in an
open interval `(a, c) ⊆ [loS, hiS]` on which `S` is strictly increasing, and let
`S′(y) > 0`. Then:
1. for every reservation price `v`, the buyer's expected profit `b ↦ π_b(b, v)` is
   differentiable at `b = S(y)` with derivative
   `(v − S(y)) · f_b(y)/S′(y) − k · F_b(y)`;
2. if `(S, B)` is an equilibrium, then for every buyer value `x ∈ [loB, hiB]` whose offer
   is `B(x) = S(y)` this derivative vanishes at `v = x`.

*Formalization Note.* `S′(y) > 0` is not in the paper's statement; it is what makes the
offer density `g_b(S(y)) = f_b(y)/S′(y)` finite, which the paper's display uses. The value
`x` with `B x = S y` is the paper's `v_b = B⁻¹(S(y))`, taken as a bound variable. -/
theorem buyer_first_order_condition (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fb S B : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hS : ClassA S loS hiS)
    (a c y : ℝ) (ha : loS ≤ a) (hc : c ≤ hiS) (hy : y ∈ Ioo a c)
    (hmono : StrictMonoOn S (Ioo a c)) (hderiv : 0 < deriv S y) :
    (∀ v : ℝ, HasDerivAt (fun b => Shared.buyerProfit k μb S b v)
        ((v - S y) * (fb y / deriv S y) - k * cdf μb y) (S y)) ∧
      (Shared.IsEquilibrium k μb μs loS hiS loB hiB S B →
        ∀ x ∈ Icc loB hiB, B x = S y →
          (x - S y) * (fb y / deriv S y) - k * cdf μb y = 0) := by sorry

end ChatterjeeSamuelson.LinkedODE
