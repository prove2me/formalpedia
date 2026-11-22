-- Prove2me | Theorems.Thm_CGWH_cofiniteTopology_not_weaklyHausdorffSpace
-- name    : CGWH.cofiniteTopology_not_weaklyHausdorffSpace
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:55.206849+00:00
-- url     : https://prove2.me/theorems/533665b4-966f-44c1-9401-5186ed4194f8
-- title:
--   The cofinite topology on an infinite set is $T_1$ but neither weakly Hausdorff nor $k$-Hausdorff
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$. For spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology.
--
--   A counter-example showing that the weak Hausdorff condition is strictly stronger than the $T_1$ separation axiom.
--
--   Let $X$ be an infinite set and endow it with the *cofinite topology*: the closed subsets are the finite subsets of $X$ and $X$ itself. Every point of this space is closed, so it is a $T_1$ space.
--
--   **Statement.** Let $X$ be an infinite set with the cofinite topology. Then:
--
--   1. $X$ is not weakly Hausdorff: there are a compact Hausdorff space $K$ and a continuous map $g:K\to X$ whose image $g(K)$ is not closed in $X$;
--   2. the diagonal $\Delta_X=\{(x,x):x\in X\}$ is not $k$-closed in $X\times_0X$, i.e. $X$ is not even $k$-Hausdorff.
--
--   Since every weakly Hausdorff space is $T_1$ and has a $k$-closed diagonal, this locates the weak Hausdorff condition strictly between $T_1$ and $T_2$ (the one-point compactification of $\mathbf Q$ is weakly Hausdorff and not Hausdorff). The source states the example in the form "$X$ is $T_1$, but not weakly Hausdorff (it violates Lemma E.2.1.6(2))", where Lemma E.2.1.6(2) is the $k$-closedness of the diagonal.
--
--   **Formalization Note.** `CofiniteTopology X` is Mathlib's type synonym of `X` carrying the cofinite topology, for `X : Type u` with `[Infinite X]`; its `T1Space` instance is in Mathlib and is therefore not part of the formal conclusion. `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (test spaces: compact Hausdorff spaces of `Type u`). Part 2 is written `¬ IsClosed[TopologicalSpace.compactlyGenerated.{u} (CofiniteTopology X × CofiniteTopology X)] (Set.diagonal (CofiniteTopology X))`: the product carries the product topology of the two cofinite topologies and `compactlyGenerated` is its $k$-ification.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 848, Example E.2.1.8

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem cofiniteTopology_not_weaklyHausdorffSpace (X : Type u) [Infinite X] :
    ¬ WeaklyHausdorffSpace (CofiniteTopology X) ∧
      ¬ IsClosed[TopologicalSpace.compactlyGenerated.{u}
          (CofiniteTopology X × CofiniteTopology X)] (Set.diagonal (CofiniteTopology X)) := by
  sorry

end CGWH
