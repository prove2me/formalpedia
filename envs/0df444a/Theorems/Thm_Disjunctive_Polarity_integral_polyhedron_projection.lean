-- Prove2me | Theorems.Thm_Disjunctive_Polarity_integral_polyhedron_projection
-- name    : Disjunctive.Polarity.integral_polyhedron_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:16:37.492551+00:00
-- url     : https://prove2.me/theorems/9eec0b79-97ba-4e95-85a2-fc617378c3e4
-- title:
--   Proposition 2.6 — projection of an integral polyhedron
-- statement:
--   This is Proposition 2.6 of Balas's *Disjunctive Programming*: integrality of a polyhedron is
--   preserved under projection.
--
--   If $Q$ is an **integral** polyhedron (every extreme point has integer coordinates), then
--   $\mathrm{Proj}_x(Q)$ is also integral.
--
--   This follows from the simple observation that every extreme point $x$ of $\mathrm{Proj}_x(Q)$
--   lifts to an extreme point or extreme ray of $Q$ itself: if $Q$'s vertices are all integral, so is
--   every such lift, hence so is $x$.
--
--   **Formalization Note.** `IsIntegralPair` is the analogue of `IsIntegral` for the two-coordinate
--   space $(\mathrm{Fin}\,p \to \mathbb{R}) \times (\mathrm{Fin}\,q \to \mathbb{R})$ that `Poly2`
--   lives in.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 28, Proposition 2.6

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- Proposition 2.6 (Balas §2.2, p. 28): the projection of an integral polyhedron is integral. -/
theorem integral_polyhedron_projection {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hInt : IsIntegralPair (Poly2 A B b)) :
    IsIntegral (ProjOntoX (Poly2 A B b)) := by sorry

end Disjunctive.Polarity
