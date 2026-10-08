-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_polymatroid_union_lifted_v2
-- name    : Disjunctive.Polymatroids.polymatroid_union_lifted_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:53.490994+00:00
-- url     : https://prove2.me/theorems/4ef6b030-5368-4e79-b23c-e8996fcc48f7
-- title:
--   Corollary 13.21 — lifted description of $\mathrm{conv}(P(r_1)\cup P(r_2))$ via $\mathrm{conv}\,Z(r_1,r_2)$
-- statement:
--   This is Corollary 13.21 of Balas's *Disjunctive Programming*: the same-ground-set specialization of Proposition 13.16, obtained through the same-space reduction of Theorem 13.18.
--
--   Let $r_1,r_2$ be set functions on $N=\{1,\dots,n\}$ satisfying conditions 1-3 of Application 1: $r(\emptyset)=0$, $r(A)\le|A|$ for $A\subsetneq N$, and $r$ nondecreasing. Let $P(r_i) := \{x\in[0,1]^n : x(A)\le r_i(A)\ \forall A\subseteq N\}$ be the corresponding polytopes in the unit cube. Then $\mathrm{conv}(P(r_1)\cup P(r_2))$ is the set of $w\in[0,1]^n$ for which there exist $x,y\in[0,1]^n$ with
--   $$
--   w = x + y - \mathbf 1
--   $$
--   and
--   $$
--   \frac{|A|-x(A)}{|A|-r_1(A)} + \frac{|B|-y(B)}{|B|-r_2(B)} \ \ge\ 1 \qquad \forall A,B\subseteq N \text{ with } r_1(A)<|A|,\ r_2(B)<|B| .
--   $$
--   By Proposition 13.16 the last two conditions say exactly that $(x,y)\in\mathrm{conv}\,Z(r_1,r_2)$. In the complemented variables $\bar w = \mathbf 1-w$, $\bar x=\mathbf 1-x$, $\bar y=\mathbf 1-y$, where the polytopes become upper monotone and Theorem 13.18 applies, the relation reads $\bar w=\bar x+\bar y$.
--
--   **Formalization Note.** The retired version wrote $w = x + y$ in the original variables and put no box constraints on $x, y$. Then for $r_1=r_2\equiv0$ it admitted $w=1$ although $\mathrm{conv}(P(r_1)\cup P(r_2))=\{0\}$. The polymatroid-type polytopes $P(r_i)$ are lower monotone, while Theorem 13.18 is stated for upper monotone polytopes, so the reduction must be applied in complemented variables. Translated back, this gives $w = x+y-\mathbf 1$ with $(x,y)\in\mathrm{conv}\,Z\subseteq[0,1]^{2n}$; the box constraints of Proposition 13.16 are now explicit. As in Application 1, the polytopes are taken inside $[0,1]^n$, i.e. $P(r_i)\cap[0,1]^n$. For $n\ge2$ this is automatic from $r(\{j\})\le1$, and for $n=1$ it is the reading under which the right-hand side, a subset of $[0,1]^n$, can match.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §13.7, p. 231, Corollary 13.21 (with Proposition 13.16 and Theorem 13.18) — corrected transcription: the reduction w̄ = x̄ + ȳ of Theorem 13.18 is applied in complemented variables, i.e. w = x + y − 1 in the original ones

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Corollary 13.21 (Balas, *Disjunctive Programming*, Springer 2018, §13.7, p. 231): for set
functions `r₁, r₂` on `N` satisfying conditions 1-3 of Application 1, with the two polytopes
`P(r₁), P(r₂)` taken inside `[0,1]ⁿ` as in Application 1,
`conv(P(r₁) ∪ P(r₂))` is the set of `w ∈ [0,1]ⁿ` such that `w = x + y - 𝟙` for some
`(x, y) ∈ [0,1]ⁿ × [0,1]ⁿ` satisfying
`(|A| - x(A))/(|A| - r₁(A)) + (|B| - y(B))/(|B| - r₂(B)) ≥ 1` for all `A, B ⊆ N` with
`r₁(A) < |A|`, `r₂(B) < |B|`; i.e. `(x, y) ∈ conv Z(r₁, r₂)` by Proposition 13.16. In the
complemented variables `w̄ = 𝟙 - w`, `x̄ = 𝟙 - x`, `ȳ = 𝟙 - y` in which the book's Theorem 13.18
(for upper monotone polytopes) is applied, this is the book's `w̄ = x̄ + ȳ`.

Correction w.r.t. the retired version: the retired statement wrote `w = x + y` in the original
variables and dropped the box constraints `0 ≤ x, y ≤ 𝟙` of `conv Z(r₁, r₂)`; then for
`r₁ = r₂ = 0` the point `w = 1` was admitted although `conv(P(r₁) ∪ P(r₂)) = {0}`. -/
theorem polymatroid_union_lifted_v2 {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2) :
    convexHull ℝ ((PolymatroidP r1 ∩ {x | ∀ i, x i ≤ 1}) ∪
        (PolymatroidP r2 ∩ {x | ∀ i, x i ≤ 1})) =
      {w : Fin n → ℝ | (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
        ∃ x y : Fin n → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
          (∀ i, w i = x i + y i - 1) ∧
          ∀ A B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
            1 ≤ ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) +
              ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B)} := by sorry

end Disjunctive.Polymatroids
