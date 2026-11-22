-- Prove2me | Theorems.Thm_CGWH_weaklyHausdorffSpace_quotient_iff
-- name    : CGWH.weaklyHausdorffSpace_quotient_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:16.127302+00:00
-- url     : https://prove2.me/theorems/ff117ce6-770f-4f5f-baf0-a66199fe5e4a
-- title:
--   A quotient $X/R$ of a compactly generated space is weakly Hausdorff iff $R$ is closed in $X\times X=k(X\times_0X)$
-- statement:
--   Criterion for a quotient of a compactly generated space to be weakly Hausdorff.
--
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$. For spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology and $X\times Y:=k(X\times_0Y)$, which is the product in the category $\mathbf{CG}$ of compactly generated spaces when $X$ and $Y$ are compactly generated.
--
--   **Statement.** Let $X$ be a compactly generated topological space and let $R\subseteq X\times X$ be an equivalence relation on $X$. Endow $X/R$ with the quotient topology. The following are equivalent:
--
--   1. the quotient space $X/R$ is weakly Hausdorff;
--   2. $R$ is a closed subset of $X\times X=k(X\times_0X)$, i.e. $R$ is a $k$-closed subset of $X\times_0X$.
--
--   No separation hypothesis is made on $X$. Since quotients of compactly generated spaces are compactly generated, the criterion says that the quotients of $X$ lying in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces are exactly the quotients by *closed* equivalence relations. This is what makes the weak Hausdorffification $h(X)=X/R_X$ (quotient by the smallest closed equivalence relation) work, and it is the reason why $\mathbf{CGWH}$, unlike the category of compactly generated Hausdorff spaces, is stable under quotients by closed equivalence relations and under pushouts along closed embeddings. The paper uses it in Proposition E.2.1.13, Remark E.2.2.3 and Lemma E.2.3.10.
--
--   **Formalization Note.** All spaces live in one universe `u`; `CompactlyGeneratedSpace` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (closed images of all continuous maps from compact Hausdorff spaces of `Type u`). The equivalence relation is a `Setoid X`, the quotient `Quotient S` carries Mathlib's quotient topology, and `{p : X × X | S p.1 p.2}` is the graph of the relation; it is required to be closed for `TopologicalSpace.compactlyGenerated (X × X)`, the $k$-ification of the product topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 848, Lemma E.2.1.11; classical reference (as cited by the paper at this place): N. Strickland, The category of CGWH spaces (available online), Prop. 2.17, Prop. 2.20 and Cor. 2.21

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem weaklyHausdorffSpace_quotient_iff
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedSpace X] (S : Setoid X) :
    WeaklyHausdorffSpace (Quotient S) ↔
      IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] {p : X × X | S p.1 p.2} := by sorry

end CGWH
