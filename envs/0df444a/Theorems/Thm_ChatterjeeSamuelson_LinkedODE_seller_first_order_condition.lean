-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_LinkedODE_seller_first_order_condition
-- name    : ChatterjeeSamuelson.LinkedODE.seller_first_order_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:48:17.067264+00:00
-- url     : https://prove2.me/theorems/42f5f242-f761-402a-a4d3-e8fb18df5e70
-- title:
--   Proof of Theorem 2: the seller's first-order condition
-- statement:
--   Let $0 \le k \le 1$. Let the seller's belief $\mu_s$ about the buyer's value be a regular belief on $[\underline v_b, \bar v_b]$ with distribution function $F_s$ and density $f_s$, and let the buyer's strategy $B$ be of class $A$ on $[\underline v_b, \bar v_b]$. Let $x$ lie in an open interval $(a, c) \subseteq [\underline v_b, \bar v_b]$ on which $B$ is strictly increasing, and suppose $B'(x) > 0$. Then:
--
--   1. for every reservation price $v$, the seller's expected profit $s \mapsto \pi_s(s, v)$ is differentiable at $s = B(x)$, with
--   $$
--   \frac{\partial \pi_s}{\partial s}(B(x), v) = \bigl(v - B(x)\bigr)\frac{f_s(x)}{B'(x)} + (1-k)\bigl(1 - F_s(x)\bigr);
--   $$
--   2. if $(S, B)$ is an equilibrium, then for every seller value $y \in [\underline v_s, \bar v_s]$ with $S(y) = B(x)$,
--   $$
--   \bigl(y - B(x)\bigr)\frac{f_s(x)}{B'(x)} + (1-k)\bigl(1 - F_s(x)\bigr) = 0.
--   $$
--
--   This is the paper's first-order condition $(v_s - s) g_s(s) + (1-k)(1 - G_s(s)) = 0$ at $s = B(x)$, with $g_s(s) = f_s(x)/B'(x)$ and $G_s(s) = F_s(x)$; rearranged, it is equation (3b).
--
--   **Formalization Note** The hypothesis $B'(x) > 0$ is not stated in the paper; it makes the offer density finite. The seller value $y$ with $S(y) = B(x)$ is the paper's $S^{-1}(B(x))$.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 840 [PDF 6], proof of Theorem 2, display "∂π_s/∂s = (v_s − s)g_s(s) + (1 − k)(1 − G_s(s)) = 0"

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- The seller's first-order condition (Chatterjee & Samuelson, *Bargaining under
Incomplete Information*, Oper. Res. 31(5) 1983, §2, p. 840 [PDF 6], proof of Theorem 2,
unnumbered display "∂π_s/∂s = (v_s − s)g_s(s) + (1 − k)(1 − G_s(s)) = 0", with the dummy
variable `x = B⁻¹(s)`).

Let `0 ≤ k ≤ 1`, let the seller's belief `μs` about the buyer's value be regular on
`[loB, hiB]` with density `fs`, let `B` be of class `A` on `[loB, hiB]`, let `x` lie in an
open interval `(a, c) ⊆ [loB, hiB]` on which `B` is strictly increasing, and let
`B′(x) > 0`. Then:
1. for every reservation price `v`, the seller's expected profit `s ↦ π_s(s, v)` is
   differentiable at `s = B(x)` with derivative
   `(v − B(x)) · f_s(x)/B′(x) + (1 − k)(1 − F_s(x))`;
2. if `(S, B)` is an equilibrium, then for every seller value `y ∈ [loS, hiS]` whose ask
   is `S(y) = B(x)` this derivative vanishes at `v = y`.

*Formalization Note.* `B′(x) > 0` is not in the paper's statement; it makes the offer
density `g_s(B(x)) = f_s(x)/B′(x)` finite. `G_s(B(x)) = F_s(x)` is the paper's
"appropriate substitution"; `1 − G_s(s)` is the probability that the buyer offers at
least `s`. The value `y` with `S y = B x` is the paper's `S⁻¹(B(x))`. -/
theorem seller_first_order_condition (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fs S B : ℝ → ℝ)
    (hμs : RegularBelief μs loB hiB fs) (hB : ClassA B loB hiB)
    (a c x : ℝ) (ha : loB ≤ a) (hc : c ≤ hiB) (hx : x ∈ Ioo a c)
    (hmono : StrictMonoOn B (Ioo a c)) (hderiv : 0 < deriv B x) :
    (∀ v : ℝ, HasDerivAt (fun s => Shared.sellerProfit k μs B s v)
        ((v - B x) * (fs x / deriv B x) + (1 - k) * (1 - cdf μs x)) (B x)) ∧
      (Shared.IsEquilibrium k μb μs loS hiS loB hiB S B →
        ∀ y ∈ Icc loS hiS, S y = B x →
          (y - B x) * (fs x / deriv B x) + (1 - k) * (1 - cdf μs x) = 0) := by sorry

end ChatterjeeSamuelson.LinkedODE
