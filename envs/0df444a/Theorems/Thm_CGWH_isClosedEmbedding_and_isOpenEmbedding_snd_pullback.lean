-- Prove2me | Theorems.Thm_CGWH_isClosedEmbedding_and_isOpenEmbedding_snd_pullback
-- name    : CGWH.isClosedEmbedding_and_isOpenEmbedding_snd_pullback
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:52.043501+00:00
-- url     : https://prove2.me/theorems/d980cda9-f456-4f3b-8b49-7fb135c6347a
-- title:
--   In $\mathbf{CGWH}$, closed embeddings and open embeddings are stable under arbitrary base change
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$. For spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology.
--
--   Closed embeddings and open embeddings of compactly generated weakly Hausdorff spaces are stable under base change in the category $\mathbf{CGWH}$.
--
--   Let $X,Y,T$ be compactly generated weakly Hausdorff spaces, let $f:X\to Y$ be a map and let $g:T\to Y$ be a continuous map. The fibre product of $f$ and $g$ in $\mathbf{CGWH}$ (equivalently, in the category of compactly generated spaces) is
--   $$X\times_{f,Y,g}T:=k\big(\{(x,t)\in X\times_0T\;:\;f(x)=g(t)\}\big),$$
--   the $k$-ification of the subspace $\{f(x)=g(t)\}$ of the product space $X\times_0T$, and the base change of $f$ along $g$ is the projection
--   $$f_T:X\times_{f,Y,g}T\longrightarrow T,\qquad (x,t)\longmapsto t .$$
--
--   **Statement.**
--
--   1. If $f$ is a closed embedding, then $f_T$ is a closed embedding.
--   2. If $f$ is an open embedding, then $f_T$ is an open embedding.
--
--   In both cases the image of $f_T$ is $g^{-1}(f(X))$. These are parts (4) and (5) of the source's Lemma E.2.3.6; part (6), the stability of quotient maps under base change, is the platform statement `CGWH.isQuotientMap_snd_pullback`. Together they are the permanence properties of morphisms of $\mathbf{CGWH}$ that the paper needs to work with its sites of compactly generated weakly Hausdorff spaces (closed and open subspaces pull back to closed and open subspaces, without any correction of the topology by $k$ being visible on the target).
--
--   **Formalization Note.** All spaces live in one universe `u`; `CompactlyGeneratedSpace` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (closed images of all continuous maps from compact Hausdorff spaces of `Type u`). The fibre product is the subtype `{p : X × T // f p.1 = g p.2}` of the product, endowed with `TopologicalSpace.compactlyGenerated` of its subspace topology (the $k$-ification), exactly as in `CGWH.isQuotientMap_snd_pullback`; the map is `p ↦ p.1.2` and the target `T` carries its given topology. The hypotheses are those of the source (all three spaces compactly generated and weakly Hausdorff); `f` is any function, its continuity being part of `IsClosedEmbedding f`, resp. `IsOpenEmbedding f`. Only the base-change clause of parts (4) and (5) is stated: the clause on compositions is in Mathlib, and parts (1), (2) (injective, surjective maps) are statements about the underlying sets.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 856-857, Lemma E.2.3.6 (4) and (5); classical reference (as cited by the paper for the proof of this lemma): N. Strickland, The category of CGWH spaces (available online), Prop. 2.32

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isClosedEmbedding_and_isOpenEmbedding_snd_pullback
    {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    [CompactlyGeneratedSpace T] [WeaklyHausdorffSpace T]
    {f : X → Y} {g : T → Y} (hg : Continuous g) :
    (IsClosedEmbedding f →
        @IsClosedEmbedding {p : X × T // f p.1 = g p.2} T
          (TopologicalSpace.compactlyGenerated.{u} {p : X × T // f p.1 = g p.2}) _
          (fun p => p.1.2)) ∧
      (IsOpenEmbedding f →
        @IsOpenEmbedding {p : X × T // f p.1 = g p.2} T
          (TopologicalSpace.compactlyGenerated.{u} {p : X × T // f p.1 = g p.2}) _
          (fun p => p.1.2)) := by sorry

end CGWH
