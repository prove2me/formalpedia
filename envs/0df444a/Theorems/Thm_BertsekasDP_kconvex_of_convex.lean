-- Prove2me | Theorems.Thm_BertsekasDP_kconvex_of_convex
-- name    : BertsekasDP.kconvex_of_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:37:50.482711+00:00
-- url     : https://prove2.me/theorems/23886caf-4cf2-41f4-9f7f-98fd84be97d2
-- title:
--   Convex ⟹ K-convex (Lemma 4.2.1(a))
-- statement:
--   **Lemma 4.2.1(a).** Every real-valued convex function $g$ on the line is $0$-convex, and hence $K$-convex for every $K \ge 0$:
--
--   $$g(y) + \frac{z}{b}\bigl(g(y) - g(y-b)\bigr) \;\le\; K + g(z+y) \qquad \text{for all } z \ge 0, \; b > 0, \; y \in \mathbb{R}, \; K \ge 0.$$
--
--   The content is that $K$-convexity genuinely generalizes convexity, so the machinery developed for fixed ordering costs applies verbatim to the zero-fixed-cost case treated earlier in §4.2. Concretely, the chord slope of a convex function over $[y-b,y]$ never exceeds its average rate of increase to the right of $y$, which is the inequality above with $K = 0$; enlarging $K$ only weakens it.
--
--   **Formalization Note** Convexity is assumed on all of $\mathbb{R}$ in Mathlib's sense, with no continuity hypothesis added. The conclusion is stated as a conjunction — the $K=0$ case and the case of arbitrary $K \ge 0$ — even though the first is the instance $K = 0$ of the second.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Lemma 4.2.1(a)

import Mathlib
import Definitions.Def_BertsekasKConvex

namespace BertsekasDP

theorem kconvex_of_convex (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) :
    BertsekasKConvex 0 g ∧ ∀ K : ℝ, 0 ≤ K → BertsekasKConvex K g := by sorry

end BertsekasDP
