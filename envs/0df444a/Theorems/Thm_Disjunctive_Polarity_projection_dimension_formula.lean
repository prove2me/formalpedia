-- Prove2me | Theorems.Thm_Disjunctive_Polarity_projection_dimension_formula
-- name    : Disjunctive.Polarity.projection_dimension_formula
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:17:08.086006+00:00
-- url     : https://prove2.me/theorems/3f65c1ac-0ff9-4a62-8fa9-9b2bde7ba43d
-- title:
--   Theorem 2.7 — the dimension of a projection
-- statement:
--   This is Theorem 2.7 of Balas's *Disjunctive Programming*: an exact formula for how projection
--   affects dimension.
--
--   $$
--   \dim(\mathrm{Proj}_x(Q)) = \dim(Q) - p + r^*,
--   $$
--
--   where $p$ is the number of variables projected out and $r^*$ is the rank of the $u$-columns of
--   $Q$'s equality subsystem. In particular, the projection is dimension-preserving,
--   $\dim(\mathrm{Proj}_x(Q)) = \dim(Q)$, exactly when $r^* = p$, i.e. when $A_=$ has full column
--   rank.
--
--   **Formalization Note.** `EqRankA A B b` is $r^*$; the theorem is stated for `Poly2 A B b`
--   nonempty, matching the book's standing assumption $Q \ne \emptyset$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 29, Theorem 2.7

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Theorem 2.7 (Balas §2.2.2, p. 29): the dimension of the projection of `Q` equals the
dimension of `Q`, minus the number of variables projected out, plus the rank of the `u`-columns
of `Q`'s equality subsystem. -/
theorem projection_dimension_formula {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hQ : (Poly2 A B b).Nonempty) :
    PolyDim (ProjOntoX (Poly2 A B b)) = PolyDim (Poly2 A B b) - (p : ℤ) + (EqRankA A B b : ℤ) := by sorry

end Disjunctive.Polarity
