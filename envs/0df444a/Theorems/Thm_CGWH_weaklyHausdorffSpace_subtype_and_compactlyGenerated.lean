-- Prove2me | Theorems.Thm_CGWH_weaklyHausdorffSpace_subtype_and_compactlyGenerated
-- name    : CGWH.weaklyHausdorffSpace_subtype_and_compactlyGenerated
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:46.714+00:00
-- url     : https://prove2.me/theorems/e9ac6a82-bb9a-44c4-9acd-5350bf5f81c9
-- title:
--   Subspaces and the $k$-ification of a weakly Hausdorff space are weakly Hausdorff
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$.
--
--   Two permanence properties of the weak Hausdorff condition, for an arbitrary topological space.
--
--   **Statement.** Let $X$ be a weakly Hausdorff topological space. Then:
--
--   1. every subset $A\subseteq X$, endowed with the subspace topology, is weakly Hausdorff;
--   2. the $k$-ification $k(X)$ is weakly Hausdorff.
--
--   In formulas: for every test map $g:K\to A$ (resp. $g:K\to k(X)$) the image $g(K)$ is closed in $A$ (resp. in $k(X)$).
--
--   Part 1 shows that closed and open subspaces of compactly generated weakly Hausdorff spaces (which are compactly generated) are again compactly generated weakly Hausdorff. Part 2 is what makes the $k$-ified products and fibre products of weakly Hausdorff spaces weakly Hausdorff, i.e. it is the reason why limits in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces are obtained by applying $k$ to the limits of topological spaces; the paper uses both facts throughout its Appendix E.
--
--   **Formalization Note.** `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff`; for `X : Type u` its test spaces are the compact Hausdorff spaces of `Type u`. In part 1 the subset is `s : Set X` and the statement is about the subtype `↥s` with its subspace topology. In part 2 the $k$-ification is the type `X` with the topology `TopologicalSpace.compactlyGenerated.{u} X`, passed explicitly to the class.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 846, Remark E.2.1.2 and Lemma E.2.1.5

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem weaklyHausdorffSpace_subtype_and_compactlyGenerated
    (X : Type u) [TopologicalSpace X] [WeaklyHausdorffSpace X] :
    (∀ s : Set X, WeaklyHausdorffSpace s) ∧
      @WeaklyHausdorffSpace X (TopologicalSpace.compactlyGenerated.{u} X) := by sorry

end CGWH
