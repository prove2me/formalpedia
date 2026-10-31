-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersection_weak_duality
-- name    : CombOpt.MatroidIntersection.weak_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:15.430846+00:00
-- url     : https://prove2.me/theorems/e4072efa-fd56-4793-9a01-f2013cd1b61d
-- title:
--   §8.3 weak duality — $|J|\le r_1(A)+r_2(\bar A)$
-- statement:
--   Let $M_1=(S,\mathcal I_1)$ and $M_2=(S,\mathcal I_2)$ be matroids on the same finite set $S$, with rank functions $r_1,r_2$. For every common independent set $J\in\mathcal I_1\cap\mathcal I_2$ and every $A\subseteq S$,
--   $$|J|\le r_1(A)+r_2(\bar A),\qquad \bar A=S\setminus A.$$
--
--   This is the easy half of the Matroid Intersection Theorem: any pair $(J,A)$ with equality certifies that $J$ is a maximum common independent set.
--
--   **Formalization Note** $\bar A$ is the complement of $A$ in the finite type $S$.
--
--   Differences from the source:
--   - encoding: matroids on a finite set S (a finite set with a family of independent subsets satisfying (M0)-(M2)) → a finite type S (the whole type is the ground set) and a structure Matroid S holding the family Indep : Finset S → Prop and a proof of (M0)-(M2); reason: the same matroids: subsets of S are Finsets of the type, and the axioms are the book's
--   - encoding: Ā = S \ A → Aᶜ (complement in the finite type S); reason: S is the whole type, so S \ A = Aᶜ
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.3, p. 288 (PDF p. 295), display before Theorem 8.14

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_rank

namespace CombOpt.MatroidIntersection

/-- **Weak duality for matroid intersection: `|J| ≤ r₁(A) + r₂(Ā)`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.3,
p. 288 (PDF p. 295): "Let J ∈ I₁ ∩ I₂ and let A ⊆ S. Then J ∩ A ∈ I₁ and J ∩ Ā ∈ I₂, so
|J| = |J ∩ A| + |J ∩ Ā| ≤ r₁(A) + r₂(Ā)."

For matroids `M₁, M₂` on `S`, every common independent set `J` and every `A ⊆ S` satisfy
`|J| ≤ r₁(A) + r₂(S \ A)`.

**Formalization Note.** `Ā = S \ A` is the complement `Aᶜ` in the finite type `S`; `r_i` is
`rank M_i.Indep`. -/
theorem weak_duality {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : Matroid S)
    (J A : Finset S) (hJ₁ : M₁.Indep J) (hJ₂ : M₂.Indep J) :
    J.card ≤ rank M₁.Indep A + rank M₂.Indep Aᶜ := by sorry

end CombOpt.MatroidIntersection
