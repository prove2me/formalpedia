-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersection_matroid_intersection
-- name    : CombOpt.MatroidIntersection.matroid_intersection
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:25.259015+00:00
-- url     : https://prove2.me/theorems/08305ba1-0cc2-4cb5-9a97-125d5c3f5474
-- title:
--   Theorem 8.14 — Matroid Intersection Theorem (Edmonds)
-- statement:
--   Let $M_1=(S,\mathcal I_1)$ and $M_2=(S,\mathcal I_2)$ be matroids on the same finite set $S$, with rank functions $r_1$ and $r_2$. Then
--   $$\max\{|J| : J\in\mathcal I_1\cap\mathcal I_2\}=\min\{r_1(A)+r_2(\bar A) : A\subseteq S\},\qquad \bar A=S\setminus A.$$
--
--   Equivalently: every common independent set $J$ and every $A\subseteq S$ satisfy $|J|\le r_1(A)+r_2(\bar A)$, and some pair $(J,A)$ attains equality.
--
--   The theorem, due to Edmonds (1970), contains König's theorem on bipartite matchings and the branching problem as special cases, and underlies the polynomial-time Matroid Intersection Algorithm.
--
--   **Formalization Note** The statement is the conjunction of (1) existence of $J\in\mathcal I_1\cap\mathcal I_2$ and $A\subseteq S$ with $|J|=r_1(A)+r_2(\bar A)$, and (2) $|J|\le r_1(A)+r_2(\bar A)$ for all common independent $J$ and all $A$. Since both families are finite and nonempty, this is exactly "max = min".
--
--   Differences from the source:
--   - encoding: matroids on a finite set S (a finite set with a family of independent subsets satisfying (M0)-(M2)) → a finite type S (the whole type is the ground set) and a structure Matroid S holding the family Indep : Finset S → Prop and a proof of (M0)-(M2); reason: the same matroids: subsets of S are Finsets of the type, and the axioms are the book's
--   - encoding: Ā = S \ A → Aᶜ (complement in the finite type S); reason: S is the whole type, so S \ A = Aᶜ
--   - encoding: max{|J| : J ∈ I₁ ∩ I₂} = min{r₁(A) + r₂(Ā) : A ⊆ S} → (∃ J A, J ∈ I₁ ∩ I₂ ∧ |J| = r₁(A) + r₂(Aᶜ)) ∧ ∀ J A, J ∈ I₁ ∩ I₂ → |J| ≤ r₁(A) + r₂(Aᶜ); reason: both families are finite and nonempty, so max = min holds iff every left value is at most every right value and some pair is equal
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.14, p. 288 (PDF p. 295)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_rank

namespace CombOpt.MatroidIntersection

/-- **Theorem 8.14 (Matroid Intersection Theorem, Edmonds 1970).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 8.14, p. 288 (PDF p. 295): "For matroids M₁, M₂ on S,
max{|J| : J ∈ I₁ ∩ I₂} = min{r₁(A) + r₂(Ā) : A ⊆ S}."

For matroids `M₁, M₂` on the finite set `S`:
1. there are a common independent set `J` and a set `A ⊆ S` with `|J| = r₁(A) + r₂(S \ A)`;
2. every common independent set `J` and every `A ⊆ S` satisfy `|J| ≤ r₁(A) + r₂(S \ A)`.
Together these say that the maximum is attained, the minimum is attained, and they are equal.

**Formalization Note.** `Ā = S \ A` is the complement `Aᶜ` in the finite type `S`; `r_i` is
`rank M_i.Indep`. Both families in the book's max and min are finite and nonempty (`∅` is
common independent, `A` ranges over all subsets), so "max = min" is equivalent to the
conjunction of clause 2 (every value on the left is at most every value on the right) and
clause 1 (some pair attains equality). -/
theorem matroid_intersection {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : Matroid S) :
    (∃ J A : Finset S, M₁.Indep J ∧ M₂.Indep J ∧
      J.card = rank M₁.Indep A + rank M₂.Indep Aᶜ) ∧
    ∀ J A : Finset S, M₁.Indep J → M₂.Indep J →
      J.card ≤ rank M₁.Indep A + rank M₂.Indep Aᶜ := by sorry

end CombOpt.MatroidIntersection
