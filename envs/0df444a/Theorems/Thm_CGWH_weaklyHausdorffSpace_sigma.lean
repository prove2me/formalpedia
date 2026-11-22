-- Prove2me | Theorems.Thm_CGWH_weaklyHausdorffSpace_sigma
-- name    : CGWH.weaklyHausdorffSpace_sigma
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:40.761038+00:00
-- url     : https://prove2.me/theorems/6245b403-8e6a-4353-9bbd-d440a4f2a9aa
-- title:
--   A disjoint union (topological coproduct) of weakly Hausdorff spaces is weakly Hausdorff
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$.
--
--   The weak Hausdorff condition is stable under topological coproducts.
--
--   **Statement.** Let $(X_i)_{i\in I}$ be a family of weakly Hausdorff topological spaces indexed by a set $I$. Then the disjoint union
--   $$\coprod_{i\in I}X_i,$$
--   endowed with the disjoint union topology (a subset is open if and only if its trace on every $X_i$ is open), is weakly Hausdorff.
--
--   A disjoint union of compactly generated spaces is compactly generated, so the statement shows that the coproduct of a family of compactly generated weakly Hausdorff spaces formed in the category of topological spaces is compactly generated weakly Hausdorff, and hence is their coproduct in the category $\mathbf{CGWH}$. This is the content of the source's Corollary E.2.2.9(2); it is the reason why, unlike general colimits (which in $\mathbf{CGWH}$ require the weak Hausdorffification functor), coproducts in $\mathbf{CGWH}$ need no special notation in the paper.
--
--   **Deviation from the source.** The source assumes the spaces $X_i$ compactly generated (they are objects of $\mathbf{CGWH}$); compact generation is not needed for the weak Hausdorff conclusion and is not assumed in the formal statement.
--
--   **Formalization Note.** The index type `ι` and all `X i` live in `Type u`; the disjoint union is the sigma type `Σ i, X i` with Mathlib's sigma topology. `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (test spaces: compact Hausdorff spaces of `Type u`). Compact generation of the sigma type of compactly generated spaces is an instance of Mathlib and is not restated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 854, Corollary E.2.2.9(2)

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem weaklyHausdorffSpace_sigma
    {ι : Type u} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, WeaklyHausdorffSpace (X i)] : WeaklyHausdorffSpace (Σ i, X i) := by sorry

end CGWH
