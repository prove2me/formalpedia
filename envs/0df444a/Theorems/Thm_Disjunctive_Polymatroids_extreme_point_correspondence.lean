-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_extreme_point_correspondence
-- name    : Disjunctive.Polymatroids.extreme_point_correspondence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:13:56.854407+00:00
-- url     : https://prove2.me/theorems/93475ed1-1a07-4b0e-9899-b631e7b26393
-- title:
--   Proposition 13.23 — extreme points of Π correspond to extreme points of U
-- statement:
--   This is Proposition 13.23 of Balas's *Disjunctive Programming*: every extreme point of $\Pi$
--   arises from an extreme point of the (much lower-dimensional, in $u$) polytope $U := \{u\ge0 :
--   \sum_A u_Ar_i(A)\le1,\ i=1,2\}$, via the same linear map $\pi_j = \sum_{A\ni j}u_A$ that
--   Proposition 13.22's projection uses.
--
--   The book's proof: since $\Pi$'s defining polytope (for fixed $u$) is monotone (upper-monotone
--   in $\pi$), any $\pi$ strictly below $\sum_{A\ni j}u_A$ for some $j$ is a nontrivial convex
--   combination, hence not extreme unless equality holds throughout; and if $u = \tfrac12u^1 +
--   \tfrac12u^2$ for distinct $u^1,u^2\in U$, the corresponding $\pi^1,\pi^2\in\Pi$ average to
--   $\pi$, so $\pi$ is not extreme unless $u$ itself is extreme in $U$.
--
--   **Formalization Note.** Only the forward direction is asserted (an extreme point of $\Pi$
--   *comes from* an extreme point of $U$), matching the proposition's own one-directional "if"
--   statement — the book does not claim every extreme point of $U$ maps to an extreme point of
--   $\Pi$ under this map. Together with Proposition 13.22, this is what lets Theorem 13.24's proof
--   restrict attention to extreme points of the much simpler $U$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 231-232, Proposition 13.23

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.23 (Balas §13.8, p. 231-232): if `π` is an extreme point of `Π`, then `π_j =
Σ_{A∋j} u_A` for `j∈N`, with `u` extreme in `U`. -/
theorem extreme_point_correspondence {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) (pi : Fin n → ℝ)
    (hpi : pi ∈ Set.extremePoints ℝ (PiSet r1 r2)) :
    ∃ u ∈ Set.extremePoints ℝ (USet r1 r2),
      ∀ j, pi j = ∑ A ∈ Finset.univ.filter (fun A => j ∈ A), u A := by sorry

end Disjunctive.Polymatroids
