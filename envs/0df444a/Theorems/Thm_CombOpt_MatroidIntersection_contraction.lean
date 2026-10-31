-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersection_contraction
-- name    : CombOpt.MatroidIntersection.contraction
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:17.099585+00:00
-- url     : https://prove2.me/theorems/e17e3de9-96e3-4a4e-a750-e3dc8512da1f
-- title:
--   Theorem 8.11 — the contraction $M/B$ is a matroid, independent of the basis, with $r'(A)=r(A\cup B)-r(B)$
-- statement:
--   Let $M=(S,\mathcal I)$ be a matroid with rank function $r$, let $B\subseteq S$, choose a basis $J$ of $B$, and define $M'=(S',\mathcal I')$ by $S'=S\setminus B$ and $\mathcal I'=\{J'\subseteq S' : J'\cup J\in\mathcal I\}$. Then
--
--   1. $M'$ is a matroid;
--   2. $M'$ does not depend on $J$: every basis $J_0$ of $B$ gives the same family $\mathcal I'$;
--   3. the rank function $r'$ of $M'$ is given by
--   $$r'(A)=r(A\cup B)-r(B)\qquad\text{for all } A\subseteq S\setminus B.$$
--
--   The matroid $M'$ is the contraction $M/B$. The proof of the Matroid Intersection Theorem uses contraction of a single element.
--
--   **Formalization Note** A basis of $B$ is a maximal independent subset of $B$ (the published `EdmondsPartition.Main.IsMaxIndepIn`). $S'$ is the subtype of elements outside $B$, and a subset of $S'$ is mapped into $S$ to form $A\cup B$. The rank formula is stated as $r'(A)+r(B)=r(A\cup B)$, avoiding truncated subtraction in $\mathbb N$.
--
--   Differences from the source:
--   - encoding: matroids on a finite set S (a finite set with a family of independent subsets satisfying (M0)-(M2)) → a finite type S (the whole type is the ground set) and a structure Matroid S holding the family Indep : Finset S → Prop and a proof of (M0)-(M2); reason: the same matroids: subsets of S are Finsets of the type, and the axioms are the book's
--   - encoding: S′ = S\B → the subtype {x : S // x ∉ B}, with subsets mapped into S by the subtype embedding; reason: the same set of elements
--   - encoding: M′ does not depend on J → for every basis J₀ of B, contractIndep M.Indep B J₀ = contractIndep M.Indep B J; reason: the ground set S′ does not involve J, so independence of the choice is equality of the families
--   - encoding: r′(A) = r(A ∪ B) − r(B) → rank I′ A + rank M.Indep B = rank M.Indep (A ∪ B); reason: equivalent over ℕ since both sides are natural numbers; avoids truncated subtraction
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.11, p. 285 (PDF p. 292)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_rank
import Definitions.Def_CombOpt_MatroidIntersection_contractIndep

namespace CombOpt.MatroidIntersection

/-- **Theorem 8.11: the contraction `M / B` is a matroid, independent of the chosen basis, with
rank function `r′(A) = r(A ∪ B) − r(B)`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 8.11, p. 285 (PDF p. 292). Setting: "Let M = (S, I) be a matroid and B ⊆ S. Choose a
basis J of B and define M′ = (S′, I′) by S′ = S\B and I′ = {J′ ⊆ S′ : J′ ∪ J ∈ I}."
"Theorem 8.11 M′ defined above is a matroid that does not depend on J, and its rank function r′
is given by r′(A) = r(A ∪ B) − r(B), for all A ⊆ S\B."

For a matroid `M` on `S`, a set `B ⊆ S` and a basis `J` of `B` (a maximal independent subset of
`B`, the published `EdmondsPartition.Main.IsMaxIndepIn M.Indep B J`):
1. the family `I′ = contractIndep M.Indep B J` on `S′ = S \ B` satisfies (M0)–(M2);
2. every basis `J₀` of `B` gives the same family `I′`;
3. for every `A ⊆ S \ B`, `r′(A) + r(B) = r(A ∪ B)`, where `r′ = rank I′`.

**Formalization Note.** `S′` is the subtype `{x : S // x ∉ B}` and `A ∪ B` maps `A` back into
`S`. The rank formula is written `r′(A) + r(B) = r(A ∪ B)`, which is the book's
`r′(A) = r(A ∪ B) − r(B)` without truncated subtraction of natural numbers. -/
theorem contraction {S : Type*} [Fintype S] [DecidableEq S] (M : Matroid S) (B J : Finset S)
    (hJ : EdmondsPartition.Main.IsMaxIndepIn M.Indep B J) :
    IsMatroid (contractIndep M.Indep B J) ∧
    (∀ J₀ : Finset S, EdmondsPartition.Main.IsMaxIndepIn M.Indep B J₀ →
      contractIndep M.Indep B J₀ = contractIndep M.Indep B J) ∧
    ∀ A : Finset {x : S // x ∉ B},
      rank (contractIndep M.Indep B J) A + rank M.Indep B =
        rank M.Indep (A.map (Function.Embedding.subtype _) ∪ B) := by sorry

end CombOpt.MatroidIntersection
