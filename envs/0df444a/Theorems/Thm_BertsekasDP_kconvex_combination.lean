-- Prove2me | Theorems.Thm_BertsekasDP_kconvex_combination
-- name    : BertsekasDP.kconvex_combination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:38:17.392909+00:00
-- url     : https://prove2.me/theorems/ae4ab163-e489-42b2-b751-2edd1e63e6c8
-- title:
--   Positive combinations (Lemma 4.2.1(b))
-- statement:
--   **Lemma 4.2.1(b).** Let $g_1$ be $K$-convex and $g_2$ be $L$-convex, with $K \ge 0$ and $L \ge 0$. Then for all scalars $\alpha > 0$ and $\rho > 0$ the positive combination is $(\alpha K + \rho L)$-convex:
--
--   $$\alpha g_1 + \rho g_2 \quad \text{is} \quad (\alpha K + \rho L)\text{-convex}.$$
--
--   So the class of $K$-convex functions is closed under positive linear combinations, with the constants combining by the very same combination. This is what makes $K$-convexity usable inside a dynamic programming recursion, where each stage forms sums of a current cost and a discounted or weighted cost-to-go: the fixed-cost parameter propagates linearly rather than degrading uncontrollably.
--
--   **Formalization Note** The coefficients are only required to be strictly positive; they need not sum to $1$, so the statement covers arbitrary positive combinations, not merely convex ones.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Lemma 4.2.1(b)

import Mathlib
import Definitions.Def_BertsekasKConvex

namespace BertsekasDP

theorem kconvex_combination (K L α ρ : ℝ) (g₁ g₂ : ℝ → ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hα : 0 < α) (hρ : 0 < ρ)
    (h₁ : BertsekasKConvex K g₁) (h₂ : BertsekasKConvex L g₂) :
    BertsekasKConvex (α * K + ρ * L) (fun y => α * g₁ y + ρ * g₂ y) := by sorry

end BertsekasDP
