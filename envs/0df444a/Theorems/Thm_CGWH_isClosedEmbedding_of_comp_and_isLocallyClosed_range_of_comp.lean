-- Prove2me | Theorems.Thm_CGWH_isClosedEmbedding_of_comp_and_isLocallyClosed_range_of_comp
-- name    : CGWH.isClosedEmbedding_of_comp_and_isLocallyClosed_range_of_comp
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:53.961156+00:00
-- url     : https://prove2.me/theorems/99934078-9c3c-4edf-af46-68811c1adfb4
-- title:
--   In $\mathbf{CGWH}$: if $g\circ f$ is a closed embedding so is $f$; if $g\circ f$ is an open embedding then $f$ is a locally closed embedding
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$.
--
--   Cancellation properties of closed and open embeddings between compactly generated weakly Hausdorff spaces. An *embedding* is a homeomorphism onto its image with the subspace topology; it is a *closed* (resp. *open*) embedding if its image is closed (resp. open), and a *locally closed* embedding if its image is locally closed, i.e. the intersection of an open and a closed subset.
--
--   **Statement.** Let $X,Y,Z$ be compactly generated weakly Hausdorff spaces and let $f:X\to Y$ and $g:Y\to Z$ be continuous maps.
--
--   1. If $g\circ f$ is a closed embedding, then $f$ is a closed embedding.
--   2. If $g\circ f$ is an open embedding, then $f$ is a locally closed embedding: $f$ is an embedding and $f(X)$ is a locally closed subset of $Y$.
--
--   For Hausdorff spaces part 1 is classical; in general topological spaces only the weaker conclusion "$f$ is an embedding" holds (this is part (1) of the source's lemma, valid for all topological spaces and available in Mathlib). The statement is a consequence of the fact that continuous sections in $\mathbf{CGWH}$ are closed embeddings (Lemma E.2.3.4 of the source): over the image of $g\circ f$ the map $f$ becomes a section of $g$. Typical uses are graphs $x\mapsto(x,u(x))$ and diagonal maps, which are closed embeddings into the $k$-ified product because their composite with a projection is the identity.
--
--   **Formalization Note.** `X Y Z : Type u` with the hypotheses of the source (all three spaces compactly generated and weakly Hausdorff): `CompactlyGeneratedSpace` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (closed images of all continuous maps from compact Hausdorff spaces of `Type u`). `IsLocallyClosed s` is Mathlib's predicate `∃ U Z, IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z`. The theorem is the conjunction of the two implications.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 856, Lemma E.2.3.5 (2) and (3)

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isClosedEmbedding_of_comp_and_isLocallyClosed_range_of_comp
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    [CompactlyGeneratedSpace Z] [WeaklyHausdorffSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    (IsClosedEmbedding (g ∘ f) → IsClosedEmbedding f) ∧
      (IsOpenEmbedding (g ∘ f) → IsEmbedding f ∧ IsLocallyClosed (Set.range f)) := by sorry

end CGWH
