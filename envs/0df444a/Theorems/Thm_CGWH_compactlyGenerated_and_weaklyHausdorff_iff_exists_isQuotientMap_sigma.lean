-- Prove2me | Theorems.Thm_CGWH_compactlyGenerated_and_weaklyHausdorff_iff_exists_isQuotientMap_sigma
-- name    : CGWH.compactlyGenerated_and_weaklyHausdorff_iff_exists_isQuotientMap_sigma
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:14.833897+00:00
-- url     : https://prove2.me/theorems/1bc5ee81-f145-4a78-8808-cb154f2d8b9e
-- title:
--   A space is compactly generated weakly Hausdorff iff it is a quotient of a disjoint union of closed compact Hausdorff subspaces
-- statement:
--   Structure of compactly generated weakly Hausdorff spaces: they are the quotients of disjoint unions of their closed compact Hausdorff subspaces.
--
--   Let $X$ be a topological space. Recall that $X$ is *compactly generated* if a subset $U\subseteq X$ is open as soon as $g^{-1}(U)$ is open in $K$ for every compact Hausdorff space $K$ and every continuous map $g:K\to X$ (no separation axiom), and that $X$ is *weakly Hausdorff* if $g(K)$ is closed in $X$ for all such $(K,g)$. A *quotient map* is a surjective map $q:Y\to X$ such that $V\subseteq X$ is open if and only if $q^{-1}(V)$ is open in $Y$.
--
--   **Statement.** The following are equivalent:
--
--   1. $X$ is compactly generated and weakly Hausdorff;
--   2. there exists a set $I$ of subsets of $X$, each of which is closed in $X$ and is a compact Hausdorff space for the subspace topology, such that the canonical map
--   $$q=\coprod_{K\in I}i_K:\ \coprod_{K\in I}K\longrightarrow X,$$
--   from the topological disjoint union of the members of $I$, given on each $K$ by the inclusion $i_K:K\hookrightarrow X$, is a quotient map.
--
--   When 1 holds one may take for $I$ the set of all closed compact Hausdorff subspaces of $X$. Thus a general compactly generated space is a quotient of a disjoint union of compact Hausdorff spaces mapping to it, and the weak Hausdorff condition says precisely that these test spaces can be taken to be closed *subspaces*: a compactly generated weakly Hausdorff space has the topology coherent with the family of its closed compact Hausdorff subspaces. The paper states this as an "important structural result" for the category $\mathbf{CGWH}$.
--
--   **Formalization Note.** `I : Set (Set X)` is a set of subsets of `X`; `Σ K : I, (K : Set X)` is the disjoint union of the corresponding subtypes with Mathlib's sigma topology, and the map is `p ↦ (p.2 : X)`; `T2Space K` refers to the subspace topology of `K`. All spaces live in one universe `u`; `CompactlyGeneratedSpace` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (closed images of all continuous maps from compact Hausdorff spaces of `Type u`). The source states the equivalence of 2 with "weakly Hausdorff" for a compactly generated $X$ (Proposition E.2.1.13) and observes in Remark E.2.1.14 that 2 characterizes the combined property without assuming compact generation; the Lean statement is this combined form.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 848-849, Proposition E.2.1.13 and Remark E.2.1.14

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem compactlyGenerated_and_weaklyHausdorff_iff_exists_isQuotientMap_sigma
    (X : Type u) [TopologicalSpace X] :
    (CompactlyGeneratedSpace X ∧ WeaklyHausdorffSpace X) ↔
      ∃ I : Set (Set X), (∀ K ∈ I, IsClosed K ∧ IsCompact K ∧ T2Space K) ∧
        IsQuotientMap (fun p : (Σ K : I, (K : Set X)) => (p.2 : X)) := by sorry

end CGWH
