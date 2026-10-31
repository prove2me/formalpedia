-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersection_augmenting_path
-- name    : CombOpt.MatroidIntersection.augmenting_path
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:25.092216+00:00
-- url     : https://prove2.me/theorems/6e4ca9c4-29dc-4967-8cb6-7a81c8c45fd1
-- title:
--   Theorem 8.15 — Augmenting Path Theorem for matroid intersection
-- statement:
--   Let $M_1=(S,\mathcal I_1)$, $M_2=(S,\mathcal I_2)$ be matroids on $S$ with rank functions $r_1,r_2$, let $J\in\mathcal I_1\cap\mathcal I_2$, and let $G=G(M_1,M_2,J)$ be the auxiliary digraph. For $R$ a set of nodes, $\delta(R)$ is the set of arcs leaving $R$.
--
--   1. (a) If there exists no $(r,s)$-dipath in $G$, then $J$ is maximum (every $J'\in\mathcal I_1\cap\mathcal I_2$ has $|J'|\le|J|$); in fact, if $A\subseteq S$ and $\delta(A\cup\{r\})=\emptyset$, then
--   $$|J|=r_1(A)+r_2(\bar A).$$
--   2. (b) If there exists an $(r,s)$-dipath in $G$, then $J$ is not maximum (some $J'\in\mathcal I_1\cap\mathcal I_2$ has $|J'|>|J|$); in fact, if $r,e_1,f_1,\dots,e_m,f_m,e_{m+1},s$ is the node sequence of a chordless $(r,s)$-dipath, then
--   $$J\,\triangle\,\{e_1,f_1,\dots,e_m,f_m,e_{m+1}\}\in\mathcal I_1\cap\mathcal I_2.$$
--
--   This theorem is the basis of the Matroid Intersection Algorithm, and part (a) together with weak duality gives the Matroid Intersection Theorem.
--
--   **Formalization Note** Dipaths are recorded by their node sequences. Every $(r,s)$-dipath of $G$ has the form $r,e_1,f_1,\dots,e_{m+1},s$ with $e_i\notin J$, $f_i\in J$, because of where the arcs of $G$ go. So part (b) quantifies over all chordless $(r,s)$-dipaths, and the set $\{e_1,\dots,e_{m+1}\}$ is the set of elements of $S$ on the path. $\delta(A\cup\{r\})=\emptyset$ is spelled out: every arc whose tail is $r$ or an element of $A$ has its head equal to $r$ or in $A$.
--
--   Differences from the source:
--   - encoding: matroids on a finite set S (a finite set with a family of independent subsets satisfying (M0)-(M2)) → a finite type S (the whole type is the ground set) and a structure Matroid S holding the family Indep : Finset S → Prop and a proof of (M0)-(M2); reason: the same matroids: subsets of S are Finsets of the type, and the axioms are the book's
--   - encoding: Ā = S \ A → Aᶜ (complement in the finite type S); reason: S is the whole type, so S \ A = Aᶜ
--   - encoding: J is maximum / J is not maximum → every common independent J′ has |J′| ≤ |J| / some common independent J′ has |J| < |J′|; reason: maximum means maximum cardinality common independent set (§8.3)
--   - encoding: (r, s)-dipath; chordless (r, s)-dipath with node sequence r, e₁, f₁, …, e_{m+1}, s → a node list P with IsDipath (auxArc M₁ M₂ J) P r s, and IsChordless; {e₁, f₁, …, e_{m+1}} = innerElems P; reason: no parallel arcs in G, so a dipath is determined by its node sequence, and every (r, s)-dipath of G has the displayed alternating form
--   - encoding: δ(A ∪ {r}) = ∅ → every arc with tail r or an element of A has head r or an element of A; reason: δ(R) is the set of arcs leaving R (p. 19)
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.15, pp. 290–291 (PDF pp. 297–298)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_rank
import Definitions.Def_CombOpt_MatroidIntersection_auxArc
import Definitions.Def_CombOpt_MatroidIntersection_IsDipath
import Definitions.Def_CombOpt_MatroidIntersection_IsChordless
import Definitions.Def_CombOpt_MatroidIntersection_innerElems

namespace CombOpt.MatroidIntersection

/-- **Theorem 8.15 (Augmenting Path Theorem).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 8.15, pp. 290–291 (PDF pp. 297–298): "(a) If there exists no (r, s)-dipath in G, then
J is maximum; in fact, if A ⊆ S and δ(A ∪ {r}) = ∅, then |J| = r₁(A) + r₂(Ā).
(b) If there exists an (r, s)-dipath in G, then J is not maximum; in fact, if
r, e₁, f₁, …, e_m, f_m, e_{m+1}, s is the node-sequence of a chordless (r, s)-dipath, then
J △ {e₁, f₁, …, e_m, f_m, e_{m+1}} ∈ I₁ ∩ I₂."
Here (p. 290) `J ∈ I₁ ∩ I₂` and `G = G(M₁, M₂, J)` is the auxiliary digraph (`auxArc`).

Let `M₁, M₂` be matroids on `S` and `J` a common independent set.
(a) If `G` has no `(r, s)`-dipath, then (i) every common independent set has size at most `|J|`,
and (ii) for every `A ⊆ S` such that no arc of `G` leaves `A ∪ {r}`, `|J| = r₁(A) + r₂(S \ A)`.
(b) If `G` has an `(r, s)`-dipath, then (i) some common independent set has size larger than
`|J|`, and (ii) for every chordless `(r, s)`-dipath `P`, the set `J △ X` is independent in both
`M₁` and `M₂`, where `X` is the set of elements of `S` on `P`.

**Formalization Note.** A dipath is recorded by its node sequence (`IsDipath`); chordless means
no arc `v_i v_j` with `i + 1 < j` (`IsChordless`). Every `(r, s)`-dipath of `G` has the book's
form `r, e₁, f₁, …, e_{m+1}, s` (arcs leave `r` only to elements outside `J`, go from outside `J`
into `J` or to `s`, from `J` back outside `J`, and none leave `s`), so quantifying over all node
sequences of chordless `(r, s)`-dipaths is the book's quantification, and `innerElems P` is
`{e₁, f₁, …, e_{m+1}}`. `δ(A ∪ {r}) = ∅` (no arc with tail in `A ∪ {r}` and head outside it) is
spelled out on the arc relation. -/
theorem augmenting_path {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : Matroid S)
    (J : Finset S) (hJ₁ : M₁.Indep J) (hJ₂ : M₂.Indep J) :
    ((¬ ∃ P : List (AuxNode S), IsDipath (auxArc M₁ M₂ J) P .r .s) →
      (∀ J' : Finset S, M₁.Indep J' → M₂.Indep J' → J'.card ≤ J.card) ∧
      ∀ A : Finset S,
        (∀ u v : AuxNode S, auxArc M₁ M₂ J u v →
          (u = .r ∨ ∃ e ∈ A, u = .elem e) → (v = .r ∨ ∃ e ∈ A, v = .elem e)) →
        J.card = rank M₁.Indep A + rank M₂.Indep Aᶜ) ∧
    ((∃ P : List (AuxNode S), IsDipath (auxArc M₁ M₂ J) P .r .s) →
      (∃ J' : Finset S, M₁.Indep J' ∧ M₂.Indep J' ∧ J.card < J'.card) ∧
      ∀ P : List (AuxNode S), IsDipath (auxArc M₁ M₂ J) P .r .s →
        IsChordless (auxArc M₁ M₂ J) P →
        M₁.Indep (symmDiff J (innerElems P)) ∧ M₂.Indep (symmDiff J (innerElems P))) := by sorry

end CombOpt.MatroidIntersection
