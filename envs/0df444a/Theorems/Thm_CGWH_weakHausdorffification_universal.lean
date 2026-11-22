-- Prove2me | Theorems.Thm_CGWH_weakHausdorffification_universal
-- name    : CGWH.weakHausdorffification_universal
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:14.687729+00:00
-- url     : https://prove2.me/theorems/968f9cf6-bffa-4d1d-acbf-ddddb177b4b4
-- title:
--   The weak Hausdorffification $h(X)=X/R_X$ of a compactly generated space is compactly generated weakly Hausdorff and universal
-- statement:
--   Existence and universal property of the weak Hausdorffification of a compactly generated space.
--
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$. For spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology and $X\times Y:=k(X\times_0Y)$, which is the product in the category $\mathbf{CG}$ of compactly generated spaces when $X$ and $Y$ are compactly generated.
--
--   Let $X$ be a compactly generated space. Let $R_X\subseteq X\times X$ be the intersection of all equivalence relations on $X$ that are closed in $X\times X=k(X\times_0X)$; it is the smallest closed equivalence relation on $X$. Put
--   $$h(X):=X/R_X\quad\text{(quotient topology)},\qquad q_X:X\to h(X)\ \text{the quotient map}.$$
--
--   **Statement.**
--
--   1. $h(X)$ is compactly generated and weakly Hausdorff.
--   2. For every compactly generated weakly Hausdorff space $Y$ and every continuous map $f:X\to Y$ there exists a unique continuous map $g:h(X)\to Y$ such that $g\circ q_X=f$.
--
--   In other words $q_X:X\to h(X)$ is the universal continuous map from $X$ to a compactly generated weakly Hausdorff space, so that $X\mapsto h(X)$ is a functor $\mathbf{CG}\to\mathbf{CGWH}$, left adjoint to the inclusion $\mathbf{CGWH}\subset\mathbf{CG}$. In contrast with the $k$-ification, $h$ changes the underlying set in general. Colimits in $\mathbf{CGWH}$ are obtained by applying $h$ to the colimit formed in $\mathbf{CG}$ (equivalently in the category of all topological spaces); the paper uses $h$ in this way in Lemma E.2.2.5 and Lemma E.2.3.8.
--
--   **Formalization Note.** The statement uses the definition file `CGWH_WeakHausdorff`: `CGWH.WeakHausdorffification X` is the quotient of `X` by the setoid `CGWH.whSetoid X` (the infimum of all setoids whose graph is closed for `TopologicalSpace.compactlyGenerated (X × X)`) with the quotient topology, and `CGWH.WeakHausdorffification.mk` is $q_X$. All spaces live in one universe `u`; `CompactlyGeneratedSpace` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (closed images of all continuous maps from compact Hausdorff spaces of `Type u`). The target `Y` ranges over the spaces of the same universe as `X`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 851-853, Definition E.2.2.2, Remark E.2.2.3 and Lemma E.2.2.4; classical reference (as cited by the paper at this place): N. Strickland, The category of CGWH spaces (available online), Prop. 2.22 and Cor. 2.23

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem weakHausdorffification_universal
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedSpace X] :
    CompactlyGeneratedSpace (WeakHausdorffification X) ∧
      WeaklyHausdorffSpace (WeakHausdorffification X) ∧
      ∀ (Y : Type u) [TopologicalSpace Y] [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
        (f : C(X, Y)),
        ∃! g : C(WeakHausdorffification X, Y), ∀ x : X, g (WeakHausdorffification.mk x) = f x := by
  sorry

end CGWH
