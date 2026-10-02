-- Prove2me | Theorems.Thm_Disjunctive_ConvexHull_hull_recovers_union
-- name    : Disjunctive.ConvexHull.hull_recovers_union
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:12:34.768432+00:00
-- url     : https://prove2.me/theorems/e117725c-77d2-403a-9d0a-e2a8737875dc
-- title:
--   Theorem 2.4 — from the convex hull to the union itself
-- statement:
--   This is Theorem 2.4 of Balas's *Disjunctive Programming*, answering the natural question left
--   open by Corollary 2.2: solutions of the lifted system with $y^h_0 \in \{0,1\}$ are always
--   basic-solution-like, but what do *all* $\{0,1\}$-restricted solutions represent?
--
--   Let $Q^{**}$ be the maximal indices (Definition above) and $P^I_Q$ the lifted polyhedron
--   $(2.1)_Q$ restricted to $y^h_0 \in \{0,1\}$ for every $h \in Q$. If
--
--   $$
--   C_h = C_j \ \ \forall h,j \in Q^{**} \qquad \text{(2.5)}, \qquad\qquad C_k \subseteq C_h\ \
--   \forall k \in Q \setminus Q^*,\ h \in Q^{**} \qquad \text{(2.6)},
--   $$
--
--   then $X(P^I_Q) = F$: the $x$-projection of the integer-restricted lifted set recovers the
--   disjunctive set $F$ **exactly**, not merely its closed convex hull. In other words, under
--   (2.5)-(2.6), replacing the continuous relaxation $y^h_0 \in [0,1]$ of the lifted system with
--   the integrality restriction $y^h_0 \in \{0,1\}$ turns the lifted polyhedron's projection from a
--   description of $\mathrm{cl\,conv}(F)$ into a description of $F$ itself — showing precisely when
--   a disjunctive set can be represented as the constraint set of an integer program: exactly when,
--   in disjunctive normal form, its maximal disjuncts share a common recession cone.
--
--   **Formalization Note.** The inclusion $P^I_Q \supseteq F$ always holds and is the easy half
--   (any $x \in P_h$ extends to a tuple with $y^h_0=1$); hypotheses (2.5)-(2.6) are needed only for
--   the reverse inclusion. `IntegerRestricted` and `MaximalIndices` are the companion definitions.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 23, Theorem 2.4

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace Disjunctive.ConvexHull

/-- Theorem 2.4 (Balas §2.1.2, p. 23): if all maximal disjuncts share the same recession cone
(2.5) and every non-feasible disjunct's recession cone sits inside that common cone (2.6), then
the `x`-projection of the integer-restricted lifted polyhedron over all of `Q` recovers the
disjunctive set `F` itself, not merely its closed convex hull. -/
theorem hull_recovers_union {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (h25 : ∀ h ∈ MaximalIndices m A b, ∀ j ∈ MaximalIndices m A b, RecessionCone (A h) = RecessionCone (A j))
    (h26 : ∀ k, k ∉ FeasibleIndices m A b → ∀ h ∈ MaximalIndices m A b,
             RecessionCone (A k) ⊆ RecessionCone (A h)) :
    ProjX (IntegerRestricted (LiftedPolyhedron m A b Set.univ)) = DisjunctiveSet m A b := by sorry

end Disjunctive.ConvexHull
