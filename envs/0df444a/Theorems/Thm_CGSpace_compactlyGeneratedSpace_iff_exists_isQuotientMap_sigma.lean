-- Prove2me | Theorems.Thm_CGSpace_compactlyGeneratedSpace_iff_exists_isQuotientMap_sigma
-- name    : CGSpace.compactlyGeneratedSpace_iff_exists_isQuotientMap_sigma
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:21.559915+00:00
-- url     : https://prove2.me/theorems/2238e4b4-380e-4546-90b6-bf0bbe3a41bf
-- title:
--   A space is compactly generated iff it is a quotient of a set-indexed disjoint union of compact Hausdorff spaces
-- statement:
--   Characterization of compactly generated spaces as the quotients of set-indexed disjoint unions of compact Hausdorff spaces.
--
--   A topological space $X$ is *compactly generated* if a subset $U\subseteq X$ is open as soon as $g^{-1}(U)$ is open in $K$ for every compact Hausdorff space $K$ and every continuous map $g:K\to X$; equivalently, a map $f:X\to Y$ to an arbitrary topological space is continuous as soon as all the compositions $f\circ g$ are continuous. No separation axiom is imposed on $X$. A map $q:Y\to X$ of topological spaces is a *quotient map* (*submersive map* in the terminology of the source) if it is surjective and a subset $V\subseteq X$ is open if and only if $q^{-1}(V)$ is open in $Y$.
--
--   **Statement.** For a topological space $X$ the following are equivalent:
--
--   1. $X$ is compactly generated;
--   2. there exist a set $I$, a compact Hausdorff space $K_i$ for each $i\in I$, and a quotient map
--   $$q:\coprod_{i\in I}K_i\longrightarrow X$$
--   from the topological disjoint union of the $K_i$.
--
--   This is the equivalence of conditions (1), (3) and (4) of Lemma E.1.1.3 of the paper, on which its definition of compactly generated spaces rests. It is the basic tool for permanence properties: the paper uses it to show that colimits, closed subspaces and open subspaces of compactly generated spaces are compactly generated (Lemmas E.1.2.2 and E.1.2.25).
--
--   **Formalization Note.** `CompactlyGeneratedSpace X` is Mathlib's notion for `X : Type u`: the topology of $X$ is coinduced by all continuous maps from compact Hausdorff spaces in the same universe (`CompHaus.{u}`), with no separation axiom on $X$. The content of the statement is the size bound in $1\Rightarrow 2$: the index type `I` and the spaces `K i` live in the universe of `X` (Mathlib's definition of `TopologicalSpace.compactlyGenerated` is by a coinduced topology from a disjoint union indexed by *all* pairs $(K,g)$, an index type in `Type (u+1)`). `Topology.IsQuotientMap q` means that `q` is surjective and the topology of `X` is coinduced by `q`; `Σ i, K i` carries the disjoint union topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 828-832, Lemma E.1.1.3, equivalence of (1), (3) and (4)

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGSpace

theorem compactlyGeneratedSpace_iff_exists_isQuotientMap_sigma
    (X : Type u) [TopologicalSpace X] :
    CompactlyGeneratedSpace X ↔
      ∃ (I : Type u) (K : I → CompHaus.{u}) (q : (Σ i, K i) → X), IsQuotientMap q := by sorry

end CGSpace
