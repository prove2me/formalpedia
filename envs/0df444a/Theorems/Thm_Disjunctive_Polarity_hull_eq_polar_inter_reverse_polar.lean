-- Prove2me | Theorems.Thm_Disjunctive_Polarity_hull_eq_polar_inter_reverse_polar
-- name    : Disjunctive.Polarity.hull_eq_polar_inter_reverse_polar
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:21:47.038711+00:00
-- url     : https://prove2.me/theorems/0efbbab5-b889-44e6-b3a4-5103af885c91
-- title:
--   Corollary 2.15 — the hull as an intersection of double polars
-- statement:
--   This is Corollary 2.15 of Balas's *Disjunctive Programming*, combining the ordinary polar's
--   involution identity with Theorem 2.14's reverse-polar involution.
--
--   For any $S$ with $0 \notin \mathrm{cl}\,\mathrm{conv}(S)$:
--
--   $$
--   \mathrm{cl}\,\mathrm{conv}(S) = S^{00} \cap S^{\#\#}.
--   $$
--
--   This gives a second, purely polarity-based route to the closed convex hull, complementing the
--   lifting-and-projection route of Theorem 2.1. When $S$ is a disjunctive set $F$, the hypothesis
--   $0 \notin \mathrm{cl}\,\mathrm{conv}(F)$ is a normalization that can always be arranged without
--   changing the underlying optimization problem, not a genuine restriction.
--
--   **Formalization Note.** `Polar (Polar S)` is $S^{00}$; `ReversePolar (ReversePolar S)` is
--   $S^{\#\#}$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 33, Corollary 2.15

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

/-- Corollary 2.15 (Balas §2.4, p. 33): for any `S` with `0 ∉ cl conv S`, the closed convex hull
of `S` equals the intersection of its ordinary double polar and its reverse double polar. -/
theorem hull_eq_polar_inter_reverse_polar {n : ℕ} (S : Set (Fin n → ℝ))
    (h0 : 0 ∉ closure (convexHull ℝ S)) :
    closure (convexHull ℝ S) = Polar (Polar S) ∩ ReversePolar (ReversePolar S) := by sorry

end Disjunctive.Polarity
