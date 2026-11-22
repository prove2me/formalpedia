-- Prove2me | Theorems.Thm_CGWH_isClosed_diagonal_of_weaklyHausdorffSpace_and_iff_forall_isClosed_setOf_eq
-- name    : CGWH.isClosed_diagonal_of_weaklyHausdorffSpace_and_iff_forall_isClosed_setOf_eq
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:55.683864+00:00
-- url     : https://prove2.me/theorems/b65edfcd-de7b-49ed-a89b-1a33d63d0d19
-- title:
--   Weakly Hausdorff spaces are $k$-Hausdorff ($k$-closed diagonal), and the test-map criterion for $k$-Hausdorffness
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$. For topological spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology.
--
--   A topological space $X$ is called *$k$-Hausdorff* if its diagonal $\Delta_X=\{(x,x):x\in X\}$ is $k$-closed in $X\times_0X$, i.e. closed in $k(X\times_0X)$. The following compares this condition with the weak Hausdorff condition for an **arbitrary** topological space $X$ (no compact generation).
--
--   **Statement.** Let $X$ be a topological space and consider the conditions
--
--   1. $X$ is weakly Hausdorff;
--   2. the diagonal $\Delta_X$ is $k$-closed in $X\times_0X$ (that is, $X$ is $k$-Hausdorff);
--   3. for every compact Hausdorff space $K$ and every continuous map $g:K\to X$, the set
--   $$K\times^0_{g,X,g}K=\{(s,t)\in K\times K\;:\;g(s)=g(t)\}$$
--   is closed in $K\times_0K$.
--
--   Then $(1)\Rightarrow(2)$ and $(2)\Leftrightarrow(3)$.
--
--   For a compactly generated space $X$ one has moreover $(2)\Rightarrow(1)$ (this last assertion of the source's Lemma E.2.1.6 is a separate statement on the platform, `CGWH.weaklyHausdorffSpace_iff_isClosed_diagonal`). In general $(2)$ does not imply $(1)$: the source's Example E.2.1.10 (the one-point compactification of the Arens-Fort space) is $k$-Hausdorff and not weakly Hausdorff. The $k$-closedness of the diagonal is the form in which the weak Hausdorff condition is used in the paper: it shows that kernel pairs and equalizers of maps into a weakly Hausdorff space are $k$-closed, which gives the weak Hausdorffification functor, the closedness of sections and the description of the regular monomorphisms and epimorphisms of the category of compactly generated weakly Hausdorff spaces.
--
--   **Formalization Note.** `X : Type u` is an arbitrary topological space. "$k$-closed in $X\times_0X$" is written `IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X)`: closedness for the $k$-ification of the product topology. In condition 3 the test spaces are the compact Hausdorff spaces `K : Type u` (the universe of `X`, as in the class `CGWH.WeaklyHausdorffSpace` of the definition file `CGWH_WeakHausdorff`), the map `g : K → X` is any function assumed continuous, and the set is `{p : K × K | g p.1 = g p.2}`, closed for the product topology of `K × K`. The theorem is the conjunction of the implication $(1)\Rightarrow(2)$ and of the equivalence $(2)\Leftrightarrow(3)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 846-847, Lemma E.2.1.6 (implication (1) => (2) and equivalence (2) <=> (3)) and Remark E.2.1.7; classical reference (as cited by the paper at this place): N. Strickland, The category of CGWH spaces (available online), Prop. 2.14; C. Rezk, Compactly generated spaces (available online), Prop. 4.2

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isClosed_diagonal_of_weaklyHausdorffSpace_and_iff_forall_isClosed_setOf_eq
    (X : Type u) [TopologicalSpace X] :
    (WeaklyHausdorffSpace X →
        IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X)) ∧
      (IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X) ↔
        ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → X),
          Continuous g → IsClosed {p : K × K | g p.1 = g p.2}) := by sorry

end CGWH
