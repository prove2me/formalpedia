-- Prove2me | Theorems.Thm_AlgebraicFPT_HittingSet_component_count
-- name    : AlgebraicFPT.HittingSet.component_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:57:22.28882+00:00
-- url     : https://prove2.me/theorems/a9acf662-ef9c-41a4-a520-cd4cd03f34fb
-- title:
--   Theorem 3.2 — Component count (corrected: positive rank bound)
-- statement:
--   Let $V=\{0,\ldots,n-1\}$, $n\ge0$, and let $E$ be a finite hyperedge family on $V$ with every edge of size at most a natural number $d\ge1$. Let $k\ge0$ be natural. Form the edge ideal $I_E$ and its full complex variety as defined above.
--
--   A coordinate subspace $L_C$ is an irreducible component of $\mathcal V(I_E)$ exactly when $C$ is an inclusion-minimal hitting set, and $\operatorname{codim}L_C=|C|$. The map $C\mapsto L_C$ is a bijection between all minimal hitting sets and all components, and between their size-at-most-$k$ and codimension-at-most-$k$ subcollections. In particular,
--   $$\#\{Z\in\operatorname{Irr}(\mathcal V(I_E)):\operatorname{codim}Z\le k\}
--   =\#\mathcal H_{\le k}(E)\le d^k,$$
--   and the printed exact-size consequence also holds:
--   $$\#\mathcal H_{=k}(E)\le d^k.$$
--
--   This identifies precisely the minimal combinatorial certificates represented by the bounded-codimension geometric components. Counts cover the entire indicated collections; no chosen subcollection is substituted. Empty vertex sets and hyperedge families, empty edges and infeasible hypergraphs are all included.
--
--   **Formalization Note** Codimension is witnessed by a genuine finite Krull dimension $s$ with $s+c=n$. Cardinalities are extended naturals, so each finite bound also asserts finiteness.
--
--   Differences from the source:
--   - correction: no explicit positive rank premise → d ≥ 1; reason: for d=0, V={v}, E=∅, k=1 the zero ideal has the affine line as its sole codimension-zero component, contradicting 1 ≤ 0^1; Lemma 3.1 explicitly requires d ≥ 1
--   - encoding: finite vertex sets, the §3 component correspondence and the cumulative count in the proof preceding Theorem 3.2 → a published finite Hitting Set instance with Fin n vertices, explicit full and size-filtered bijections C ↦ L_C, cardinal equality, and extended-natural counts; reason: relabeling preserves every finite instance; §3 p.4 identifies all components and codimensions, and p.5 derives the cumulative size-at-most-k bound before the printed exact-size-k consequence
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), p.5, Theorem 3.2; component correspondence and codimension in §3, p.4

import Definitions.Def_AlgebraicFPT_HittingSet_Model
import Definitions.Def_HSElemKernel_HSInstance

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet

/-- Theorem 3.2, p.5, with the correspondence of §3, p.4.
Correction: d ≥ 1 is explicit. For d=0, E=∅, n=1, k=1 the source's geometric
bound would say the affine line has at most zero components. No other input
restrictions are added: n=0, k=0, empty E, and empty hyperedges are allowed. -/
theorem component_count (H : HSElemKernel.HSInstance) (d : ℕ) (hd : 1 ≤ d)
    (hE : ∀ e ∈ H.S, e.card ≤ d) :
    (∀ C : Finset (Fin H.n),
      (coordinateSubspace C ∈ components (edgeVariety H.S) ↔ IsMinimalHitting H.S C)) ∧
    (∀ C : Finset (Fin H.n), HasCodim (coordinateSubspace C) C.card) ∧
    Set.BijOn coordinateSubspace {C | IsMinimalHitting H.S C} (components (edgeVariety H.S)) ∧
    Set.BijOn coordinateSubspace (smallHittingSets H.S H.k) (lowComponents (edgeVariety H.S) H.k) ∧
    (lowComponents (edgeVariety H.S) H.k).encard = (smallHittingSets H.S H.k).encard ∧
    (lowComponents (edgeVariety H.S) H.k).encard ≤ (d ^ H.k : ℕ) ∧
    (exactHittingSets H.S H.k).encard ≤ (d ^ H.k : ℕ) := by sorry

end AlgebraicFPT.HittingSet
