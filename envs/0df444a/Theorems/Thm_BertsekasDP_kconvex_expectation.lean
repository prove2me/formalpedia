-- Prove2me | Theorems.Thm_BertsekasDP_kconvex_expectation
-- name    : BertsekasDP.kconvex_expectation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:39:53.779305+00:00
-- url     : https://prove2.me/theorems/17895860-bbed-4516-bf51-eb575aa802e1
-- title:
--   Expectation preserves K-convexity (Lemma 4.2.1(c))
-- statement:
--   **Lemma 4.2.1(c).** Let $g$ be $K$-convex and let $w$ be a random variable taking finitely many values, with probabilities $p_\omega \ge 0$ summing to $1$. Then the expectation
--
--   $$y \;\longmapsto\; \mathbb{E}_w\bigl[g(y - w)\bigr] \;=\; \sum_{\omega} p_\omega \, g\bigl(y - w_\omega\bigr)$$
--
--   is again $K$-convex, with the **same** constant $K$.
--
--   This is the step that carries $K$-convexity across a stage of the inventory recursion: after the ordering decision, the stock is reduced by a random demand, and the resulting expected cost-to-go must remain $K$-convex for the argument to continue by induction. That the constant does not grow is what keeps the eventual $(s,S)$ structure tied to the single fixed ordering cost.
--
--   **Formalization Note** The disturbance is finitely supported, so the expectation is a finite weighted sum and the source's integrability proviso $\mathbb{E}|g(y-w)| < \infty$ is automatic. Individual weights may be zero; the hypothesis that they sum to $1$ makes the statement vacuous over an empty outcome type.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Lemma 4.2.1(c)

import Mathlib
import Definitions.Def_BertsekasKConvex

namespace BertsekasDP

theorem kconvex_expectation {Ω : Type} [Fintype Ω] (K : ℝ) (g : ℝ → ℝ)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) (w : Ω → ℝ)
    (hg : BertsekasKConvex K g) :
    BertsekasKConvex K (fun y => ∑ ω, p ω * g (y - w ω)) := by sorry

end BertsekasDP
