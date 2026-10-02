-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_polymatroid_union_lifted
-- name    : Disjunctive.Polymatroids.polymatroid_union_lifted
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:12:56.530988+00:00
-- url     : https://prove2.me/theorems/9634d7e0-85fc-48f4-b1a0-b788d88d5af7
-- title:
--   Corollary 13.21 — the polymatroid union, lifted form
-- statement:
--   This is Corollary 13.21 of Balas's *Disjunctive Programming*: the same-space specialization of
--   Proposition 13.16, and the direct predecessor the goal theorem restates in the original
--   (unlifted) variable space.
--
--   For $r_1,r_2$ satisfying conditions 1-3 of Application 1 on the same ground set $N$,
--   $$
--   \mathrm{conv}(P(r_1)\cup P(r_2)) = \Big\{w\in[0,1]^n : w=x+y,\ \frac{|A|-x(A)}{|A|-r_1(A)} +
--   \frac{|B|-y(B)}{|B|-r_2(B)} \ge 1\ \ \forall A,B\subseteq N \text{ with } r_1(A)<|A|,\
--   r_2(B)<|B|\Big\}.
--   $$
--
--   The book derives this as "a corollary from Proposition 13.16 and Theorem 13.18" (the latter,
--   the general same-space reduction $\mathrm{conv}(P\cup Q) = \{x : x=y+w,\ (y,w)\in
--   \mathrm{conv}(Z)\}$, not drafted this pass — see `HARD.md`), applying Theorem 13.18's lifting
--   identity to Proposition 13.16's disjoint-space formula for $Z(r_1,r_2)$ with $M=N$.
--
--   **Formalization Note.** The `w=x+y` decomposition is existentially quantified, matching the
--   corollary's own "w = x+y" phrasing — the corollary describes $\mathrm{conv}(P(r_1)\cup
--   P(r_2))$ as the set of points $w$ for which *some* decomposition into $x,y$ satisfies the
--   displayed system, not that every decomposition must.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 231, Corollary 13.21

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Corollary 13.21 (Balas §13.7, p. 231): for `r₁,r₂` satisfying conditions 1-3 of Application 1,
`conv(P(r₁)∪P(r₂)) = {w∈[0,1]ⁿ : w=x+y, (|A|-x(A))/(|A|-r₁(A)) + (|B|-y(B))/(|B|-r₂(B)) ≥1 for
all A,B⊆N with r₁(A)<|A|, r₂(B)<|B|}`. -/
theorem polymatroid_union_lifted {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2) :
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {w : Fin n → ℝ | (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
        ∃ x y : Fin n → ℝ, w = x + y ∧
          ∀ A B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
            1 ≤ ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) +
              ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B)} := by sorry

end Disjunctive.Polymatroids
