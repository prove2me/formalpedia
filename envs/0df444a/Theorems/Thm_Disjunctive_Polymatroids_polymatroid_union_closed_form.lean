-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_polymatroid_union_closed_form
-- name    : Disjunctive.Polymatroids.polymatroid_union_closed_form
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:14:21.920039+00:00
-- url     : https://prove2.me/theorems/c0dccfc0-0053-41ce-8bf8-80b51ea91174
-- title:
--   Theorem 13.24 — the closed-form convex hull of a union of two polymatroids
-- statement:
--   This is Theorem 13.24 of Balas's *Disjunctive Programming*, the goal theorem of this mission
--   and the **closing result of the entire book**: a fully explicit, closed-form description of
--   the convex hull of a union of two polymatroids, in the *original* variable space (no lifting,
--   no auxiliary variables).
--
--   For polymatroid rank functions $r_1,r_2$ (satisfying $r(\emptyset)=0$, monotone, submodular),
--   $$
--   \mathrm{conv}(P(r_1)\cup P(r_2)) = \Big\{x\ge0 : x(A)\le\max\{r_1(A),r_2(A)\}\ \forall
--   A\subseteq N;\quad
--   \frac{r_2(B)-r_1(B)}{r_1(A)r_2(B)-r_1(B)r_2(A)}x(A) +
--   \frac{r_1(A)-r_2(A)}{r_1(A)r_2(B)-r_1(B)r_2(A)}x(B) \le 1
--   $$
--   $$
--   \forall A,B\subseteq N \text{ with } (r_1(A)-r_2(A))(r_1(B)-r_2(B))<0\Big\}.
--   $$
--
--   The book's proof, resting on Propositions 13.22 and 13.23, reduces to examining the extreme
--   points of $U$: a basic feasible solution has at most two nonzero components $u_A,u_B$. A
--   single nonzero $u_A = 1/\max\{r_1(A),r_2(A)\}$ yields the first family of inequalities; two
--   simultaneously nonzero $u_A,u_B$ solving $u_Ar_1(A)+u_Br_1(B)=1$, $u_Ar_2(A)+u_Br_2(B)=1$ have
--   a (unique, positive) solution exactly when $(r_1(A)-r_2(A))(r_1(B)-r_2(B))<0$, yielding the
--   second family. This generalizes an earlier result on the disjunction of matroid polyhedra
--   (proved by different means) to arbitrary polymatroids.
--
--   **Formalization Note.** `IsPolymatroidRankFunction` (not `IsApp1SetFunction`) is the correct
--   hypothesis here, matching the book's own "$r_i:2^N\to\mathbb R$ for $i=1,2$ are polymatroid
--   rank functions (satisfying 1 and 3 in Application 1 and submodular)" — this is `r(\emptyset)=0`
--   plus monotonicity plus submodularity, **not** the `r(A)\le|A|` bound of `IsApp1SetFunction`
--   (that bound is specific to the matroid-truncated special case of §13.4, not required for the
--   general polymatroid closed form). Confusing the two hypotheses here would misstate exactly
--   which set functions the theorem covers — this is the distinction `BRIEF.md` explicitly warns
--   to get right.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 232, Theorem 13.24

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Theorem 13.24 (Balas §13.8, p. 232), the goal theorem of this mission and the book's closing
result: for polymatroid rank functions `r₁,r₂`, `conv(P(r₁)∪P(r₂))` has a closed-form description
in the original variable space: `x(A)≤max{r₁(A),r₂(A)}` for every `A⊆N`, together with a two-set
inequality for every pair `A,B⊆N` with `(r₁(A)-r₂(A))(r₁(B)-r₂(B))<0`. -/
theorem polymatroid_union_closed_form {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) :
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {x : Fin n → ℝ | 0 ≤ x ∧ (∀ A : Finset (Fin n), SumOver x A ≤ max (r1 A) (r2 A)) ∧
        ∀ A B : Finset (Fin n), (r1 A - r2 A) * (r1 B - r2 B) < 0 →
          (r2 B - r1 B) / (r1 A * r2 B - r1 B * r2 A) * SumOver x A +
            (r1 A - r2 A) / (r1 A * r2 B - r1 B * r2 A) * SumOver x B ≤ 1} := by sorry

end Disjunctive.Polymatroids
