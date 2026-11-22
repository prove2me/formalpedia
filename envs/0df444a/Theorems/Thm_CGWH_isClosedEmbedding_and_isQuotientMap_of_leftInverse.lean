-- Prove2me | Theorems.Thm_CGWH_isClosedEmbedding_and_isQuotientMap_of_leftInverse
-- name    : CGWH.isClosedEmbedding_and_isQuotientMap_of_leftInverse
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:44.262296+00:00
-- url     : https://prove2.me/theorems/22166f3c-b4ec-4b8b-b29a-7e2ad7efbc93
-- title:
--   A continuous section of a continuous map out of a compactly generated weakly Hausdorff space is a closed embedding
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$.
--
--   Sections are closed embeddings: the weak Hausdorff analogue of the classical fact for Hausdorff spaces.
--
--   **Statement.** Let $X$ be a compactly generated weakly Hausdorff space, let $Y$ be a topological space, and let
--   $$g:X\to Y,\qquad f:Y\to X$$
--   be continuous maps such that $f$ is a section of $g$, i.e. $g\circ f=\mathrm{id}_Y$. Then
--
--   1. $f$ is a closed embedding: a homeomorphism of $Y$ onto the subspace $f(Y)$ of $X$, and $f(Y)=\{x\in X: f(g(x))=x\}$ is closed in $X$;
--   2. $g$ is a quotient map: $g$ is surjective and a subset $V\subseteq Y$ is open if and only if $g^{-1}(V)$ is open in $X$.
--
--   In the source the statement is made for a continuous map $g:X\to Y$ between compactly generated weakly Hausdorff spaces; a space $Y$ admitting such $f,g$ is homeomorphic to a closed subspace of $X$ and is therefore automatically compactly generated weakly Hausdorff, so no hypothesis on $Y$ is needed. The paper applies the lemma to graphs: for a continuous map $u:T\to Y$ of compactly generated weakly Hausdorff spaces, $t\mapsto(u(t),t)$ is a section of the projection $Y\times T\to T$ and hence a closed embedding, which reduces the stability of quotient maps under base change to base change along closed embeddings (Lemma E.2.3.6(6)); it also gives that a map $f$ is a closed embedding as soon as some composite $g\circ f$ is one (Lemma E.2.3.5).
--
--   **Formalization Note.** `X : Type u` carries the two hypotheses `CompactlyGeneratedSpace X` (Mathlib's notion: the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace X` (the class of the definition file `CGWH_WeakHausdorff`: closed images of all continuous maps from compact Hausdorff spaces of `Type u`); `Y : Type*` is an arbitrary topological space (deviation from the source explained above: its hypotheses on $Y$ are consequences and are dropped). `Function.LeftInverse g f` is `∀ y, g (f y) = y`. Mathlib has the corresponding statement `Function.LeftInverse.isClosedEmbedding` only for Hausdorff `X`. Part 2 holds for arbitrary topological spaces; it is included because it is part of the source's lemma.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 855-856, Lemma E.2.3.4

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isClosedEmbedding_and_isQuotientMap_of_leftInverse
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    {g : X → Y} {f : Y → X} (hg : Continuous g) (hf : Continuous f)
    (h : Function.LeftInverse g f) : IsClosedEmbedding f ∧ IsQuotientMap g := by sorry

end CGWH
