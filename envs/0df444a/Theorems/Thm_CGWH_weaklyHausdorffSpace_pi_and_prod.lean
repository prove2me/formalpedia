-- Prove2me | Theorems.Thm_CGWH_weaklyHausdorffSpace_pi_and_prod
-- name    : CGWH.weaklyHausdorffSpace_pi_and_prod
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:42.578492+00:00
-- url     : https://prove2.me/theorems/d97e2791-5f9b-4850-a278-8f328a95a6d2
-- title:
--   Arbitrary products and binary products of weakly Hausdorff spaces are weakly Hausdorff
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$.
--
--   The weak Hausdorff condition is stable under products. For topological spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology, and $\prod^0_{i\in I}X_i$ for an arbitrary product with the product topology.
--
--   **Statement.**
--
--   1. Let $(X_i)_{i\in I}$ be a family of weakly Hausdorff topological spaces indexed by a set $I$. Then the product space $\prod^0_{i\in I}X_i$ (product topology) is weakly Hausdorff.
--   2. Let $X$ and $Y$ be weakly Hausdorff topological spaces. Then $X\times_0Y$ (product topology) is weakly Hausdorff.
--
--   Since the $k$-ification of a weakly Hausdorff space is weakly Hausdorff (Lemma E.2.1.5 of the source), it follows that $k\big(\prod^0_{i}X_i\big)$ and $X\times Y:=k(X\times_0Y)$ are weakly Hausdorff as well. For compactly generated weakly Hausdorff factors these are the products in the category $\mathbf{CG}$ of compactly generated spaces, so the statement contains the source's assertion that the product formed in $\mathbf{CG}$ of a family of objects of $\mathbf{CGWH}$ computes their product in $\mathbf{CGWH}$ (Corollary E.2.2.9(1), a case of Lemma E.2.2.5(1)), and the weak Hausdorff half of Proposition E.2.3.1(2): the product space of a compactly generated weakly Hausdorff space and a locally compact Hausdorff space is compactly generated weakly Hausdorff. The paper uses these facts to compute products of the locally compact Hausdorff spaces occurring in its topological stacks inside the category of topological spaces.
--
--   **Deviation from the source.** The source states the result for compactly generated weakly Hausdorff factors and for the $k$-ified product. The formal statement is the stronger classical fact for the product topology and for arbitrary weakly Hausdorff factors (no compact generation); the source's form follows from it and from Lemma E.2.1.5.
--
--   **Formalization Note.** One theorem with two universally quantified conjuncts. In part 1 the index type `ι` and all `X i` live in `Type u`, and the product is the Pi type `∀ i, X i` with Mathlib's product topology; in part 2 the product is `X × Y` with the product topology. `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (test spaces: compact Hausdorff spaces of `Type u`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 853-855, Lemma E.2.2.5(1), Corollary E.2.2.9(1) and Proposition E.2.3.1(2)

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem weaklyHausdorffSpace_pi_and_prod :
    (∀ (ι : Type u) (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
        [∀ i, WeaklyHausdorffSpace (X i)], WeaklyHausdorffSpace (∀ i, X i)) ∧
      (∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
        [WeaklyHausdorffSpace X] [WeaklyHausdorffSpace Y], WeaklyHausdorffSpace (X × Y)) := by sorry

end CGWH
