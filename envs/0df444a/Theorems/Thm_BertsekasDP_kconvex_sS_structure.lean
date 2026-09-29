-- Prove2me | Theorems.Thm_BertsekasDP_kconvex_sS_structure
-- name    : BertsekasDP.kconvex_sS_structure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:42:44.173441+00:00
-- url     : https://prove2.me/theorems/99b1e168-76db-4be2-b57f-455473e5b6c7
-- title:
--   Structure of continuous coercive K-convex functions (Lemma 4.2.1(d))
-- statement:
--   **Lemma 4.2.1(d) (the $(s,S)$ structure).** Let $K \ge 0$ and let $g$ be a continuous $K$-convex function with $g(y) \to \infty$ as $|y| \to \infty$. Then there exist scalars $s \le S$ such that:
--
--   1. **$S$ is a global minimizer:** $g(S) \le g(y)$ for every $y$;
--   2. **$s$ is the reorder threshold, exactly $K$ above the minimum:**
--   $$g(S) + K \;=\; g(s) \;<\; g(y) \qquad \text{for every } y < s ;$$
--   3. **$g$ is non-increasing on $(-\infty, s)$;**
--   4. **no gain exceeds the fixed cost to the right of $s$:**
--   $$g(y) \;\le\; g(z) + K \qquad \text{for all } s \le y \le z .$$
--
--   These four properties are precisely what is needed to conclude that an $(s,S)$ policy is optimal: below $s$ the saving from moving to $S$ exceeds the fixed cost $K$, so one orders up to $S$; at or above $s$ property 4 says no reachable point beats the current one by more than $K$, so one does not order. This is the structural heart of Scarf's theorem on the optimality of $(s,S)$ inventory policies.
--
--   **Formalization Note** Existence is asserted, not uniqueness — several pairs $(s,S)$ may satisfy the conclusion. Property 2 is an exact equality $g(S) + K = g(s)$, not an inequality, together with a strict inequality to the left of $s$. Property 3 is stated on the open ray $(-\infty,s)$ and says nothing at $s$ itself. Coercivity is stated as divergence to $+\infty$ along both ends of the line.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Lemma 4.2.1(d)

import Mathlib
import Definitions.Def_BertsekasKConvex

namespace BertsekasDP

theorem kconvex_sS_structure (K : ℝ) (g : ℝ → ℝ) (hK : 0 ≤ K)
    (hg : BertsekasKConvex K g) (hcont : Continuous g)
    (hcoer₁ : Filter.Tendsto g Filter.atTop Filter.atTop)
    (hcoer₂ : Filter.Tendsto g Filter.atBot Filter.atTop) :
    ∃ s S : ℝ, s ≤ S ∧
      (∀ y, g S ≤ g y) ∧
      (g S + K = g s) ∧
      (∀ y < s, g s < g y) ∧
      AntitoneOn g (Set.Iio s) ∧
      (∀ y z, s ≤ y → y ≤ z → g y ≤ g z + K) := by sorry

end BertsekasDP
