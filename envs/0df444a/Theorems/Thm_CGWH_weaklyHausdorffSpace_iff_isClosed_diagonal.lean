-- Prove2me | Theorems.Thm_CGWH_weaklyHausdorffSpace_iff_isClosed_diagonal
-- name    : CGWH.weaklyHausdorffSpace_iff_isClosed_diagonal
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:10.029832+00:00
-- url     : https://prove2.me/theorems/c6a90284-061b-41d1-be52-43b088b55609
-- title:
--   A compactly generated space is weakly Hausdorff iff its diagonal is closed in $X\times X=k(X\times_0X)$
-- statement:
--   Characterization of the weak Hausdorff property of a compactly generated space by its diagonal.
--
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$. For spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology and $X\times Y:=k(X\times_0Y)$, which is the product in the category $\mathbf{CG}$ of compactly generated spaces when $X$ and $Y$ are compactly generated.
--
--   **Statement.** Let $X$ be a compactly generated topological space. Then $X$ is weakly Hausdorff if and only if the diagonal
--   $$\Delta_X=\{(x,x)\;:\;x\in X\}$$
--   is a $k$-closed subset of $X\times_0X$, i.e. a closed subset of the product $X\times X=k(X\times_0X)$ of $X$ with itself in $\mathbf{CG}$.
--
--   Since a test map into $X\times_0X$ is a pair of test maps into $X$, the condition on the diagonal says: for every compact Hausdorff space $K$ and all continuous maps $g_1,g_2:K\to X$, the coincidence set $\{t\in K: g_1(t)=g_2(t)\}$ is closed in $K$.
--
--   This is the analogue, for the category of compactly generated spaces, of the fact that a space is Hausdorff iff its diagonal is closed in the product topology (spaces whose diagonal is $k$-closed are called $k$-Hausdorff). It is the form in which the weak Hausdorff condition is used in practice: the equalizer of two continuous maps from a compactly generated space into a weakly Hausdorff space is closed, limits and function spaces of such spaces are again weakly Hausdorff, and a quotient $X/R$ is weakly Hausdorff exactly when $R$ is closed in $X\times X$. The paper uses it throughout Appendix E.2.
--
--   **Formalization Note.** All spaces live in one universe `u`; `CompactlyGeneratedSpace` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (closed images of all continuous maps from compact Hausdorff spaces of `Type u`). `IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X)` says that the diagonal is closed for the $k$-ification of the product topology of `X × X`. The paper's Lemma E.2.1.6 contains further assertions for spaces that are not compactly generated (weakly Hausdorff implies $k$-closed diagonal; a reformulation with fibre products $K\times_XK$); they are not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 846-847, Lemma E.2.1.6; classical reference (as cited by the paper at this place): N. Strickland, The category of CGWH spaces (available online), Prop. 2.14; C. Rezk, Compactly generated spaces (available online), Prop. 4.2

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem weaklyHausdorffSpace_iff_isClosed_diagonal
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedSpace X] :
    WeaklyHausdorffSpace X ↔
      IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X) := by sorry

end CGWH
