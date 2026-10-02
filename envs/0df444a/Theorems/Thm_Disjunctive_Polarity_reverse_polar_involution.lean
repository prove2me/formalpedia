-- Prove2me | Theorems.Thm_Disjunctive_Polarity_reverse_polar_involution
-- name    : Disjunctive.Polarity.reverse_polar_involution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:20:53.14562+00:00
-- url     : https://prove2.me/theorems/91abbb78-471f-4b21-87af-ebbe53dace17
-- title:
--   Theorem 2.14 — the double reverse polar
-- statement:
--   This is Theorem 2.14 of Balas's *Disjunctive Programming*: the involution property of the
--   reverse polar, in sharp contrast to the ordinary polar's $S^{00} = \mathrm{cl}\,\mathrm{conv}(S
--   \cup \{0\})$.
--
--   If $0 \notin \mathrm{cl}\,\mathrm{conv}(S)$, then
--
--   $$
--   S^{\#\#} = \mathrm{cl}\,\mathrm{conv}(S) + \mathrm{cl}\,\mathrm{cone}(S),
--   $$
--
--   the Minkowski sum of the closed convex hull of $S$ and the closure of its conic hull. Unlike the
--   ordinary polar's involution (which simply recovers $S$ itself, up to closure and convexification),
--   the reverse polar's double application recovers the hull *together with* its recession directions
--   — the extra $\mathrm{cl}\,\mathrm{cone}(S)$ summand accounts for the unbounded directions the
--   reverse-polar construction cannot see from a single application.
--
--   **Formalization Note.** `+` is the Minkowski sum (`open Pointwise`); `ConeHull` is the finite
--   nonnegative-combination conic hull.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 32, Theorem 2.14

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

open Pointwise

/-- Theorem 2.14 (Balas §2.4, p. 32): if `0 ∉ cl conv S`, the double reverse polar `S##` equals
the Minkowski sum of the closed convex hull of `S` and the closure of its conic hull. -/
theorem reverse_polar_involution {n : ℕ} (S : Set (Fin n → ℝ))
    (h0 : 0 ∉ closure (convexHull ℝ S)) :
    ReversePolar (ReversePolar S) = closure (convexHull ℝ S) + closure (ConeHull S) := by sorry

end Disjunctive.Polarity
