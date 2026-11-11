-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_6_1
-- name    : FOMCMonDep.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:32.852204+00:00
-- url     : https://prove2.me/theorems/7fe146d2-8728-42a8-a5aa-e4b6278a5c12
-- title:
--   Lemma 6.1 — tuples far from $U$ realize at most $T(q,k,c)$ types over $U$
-- statement:
--   For every $q,k,c\in\mathbb N$ there are $r=r(q)$ and $T=T(q,k,c)$ with the following property. Let $H$ be a (possibly infinite) graph expanded by at most $c$ unary predicates, $U\subseteq V(H)$ finite, $\bar u$ a tuple of vertices of $U$ of any finite length, and $F=\{a\in V(H):\mathrm{dist}_H(a,U)>r\}$. Then
--   $$\bigl|\{\mathrm{tp}^H_q(\bar a\,\bar u/U):\bar a\in F^k\}\bigr|\le T(q,k,c).$$
--   The radius $r$ depends on $q$ only, and the bound $T$ does not depend on $|U|$ or on the length of $\bar u$.
--
--   This consequence of Gaifman locality bounds the types of tuples far from the parameters in the proof of Theorem 4.4.
--
--   **Formalization Note** $r$ is chosen after $q$ alone and $T$ after $q,k,c$, both before $H$, $U$ and $\bar u$. The expansion uses $c'\le c$ predicates. Distances are in $H$; for $U=\emptyset$ all vertices are far.
--
--   Differences from the source:
--   - encoding: formulas with parameters from U (constants) → formulas whose extra free variables range over U, each assigned itself; reason: same satisfying tuples and quantifier rank, hence the same number of types
--   - encoding: a graph expanded by at most c unary predicates → MonDepMW.coloredStructure H col with c' ≤ c predicates, on any vertex type; reason: the published expansion; Part I allows infinite graphs
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 6.1, p.26 (PDF 28)

import Mathlib
import Definitions.Def_FOMCMonDep_tp
import Definitions.Def_MonDepMW_coloredGraph

set_option autoImplicit false

namespace FOMCMonDep

/-- **Lemma 6.1.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §6, p.26 (PDF 28); = Lemma B.3 with Remark B.4, proof pp.61–62
(PDF 63–64): "For every q, k, c ∈ N there are numbers r = r(q) and T = T(q, k, c) with the following property. Let H
be a graph expanded by at most c unary predicates, and let U ⊆ V(H) be finite. Fix a tuple ū of vertices of U of
finite length. Let F := {a ∈ V(H) : dist_H(a, U) > r}. Then |{tp^H_q(ā ū/U) : ā ∈ F^k}| ⩽ T(q, k, c)."

**Formalization Note.** `r` is chosen after `q` only, `T` after `q, k, c`; both before `H`, `U` and `ū`, and `ū`
has any length `m`. "Expanded by at most c unary predicates" is the published `MonDepMW.coloredStructure H col` with
`c' ⩽ c` predicates (the predicates need not be disjoint). Distances are in the graph `H` (unary predicates add no
edges to the Gaifman graph), in `ℕ∞`; for `U = ∅`, `F` is all of `V`. The tuple `ā ū` is `Fin.append ā ū`. Part I:
`H` may be infinite, and the count is an `encard`. -/
theorem lemma_6_1 (q : ℕ) :
    ∃ r : ℕ, ∀ k c : ℕ, ∃ T : ℕ, ∀ (V : Type) (H : SimpleGraph V) (c' : ℕ), c' ≤ c →
      ∀ (col : Fin c' → Set V) (U : Set V), U.Finite → ∀ (m : ℕ) (u : Fin m → V), (∀ i, u i ∈ U) →
        ((fun a : Fin k → V => tp (MonDepMW.coloredStructure H col) q (Fin.append a u) U) ''
          {a | ∀ i, ∀ x ∈ U, (r : ℕ∞) < H.edist (a i) x}).encard ≤ T := by sorry

end FOMCMonDep
