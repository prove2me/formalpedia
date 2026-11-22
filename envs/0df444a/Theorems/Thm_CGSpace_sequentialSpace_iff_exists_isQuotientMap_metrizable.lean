-- Prove2me | Theorems.Thm_CGSpace_sequentialSpace_iff_exists_isQuotientMap_metrizable
-- name    : CGSpace.sequentialSpace_iff_exists_isQuotientMap_metrizable
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:32.352873+00:00
-- url     : https://prove2.me/theorems/e58b7a91-93f3-4da8-af59-9d431267e0ce
-- title:
--   Franklin's theorem: a topological space is sequential iff it is a quotient of a locally compact metrizable space
-- statement:
--   Franklin's characterization of sequential spaces as the quotients of metrizable spaces, in its sharp form with a locally compact metrizable source.
--
--   A topological space $X$ is *sequential* if every sequentially closed subset $Z\subseteq X$ is closed, where $Z$ is sequentially closed if for every sequence $(z_n)_{n\ge0}$ in $Z$ converging to a point $x\in X$ one has $x\in Z$. A map $q:M\to X$ is a *quotient map* (*submersive* in the source) if it is surjective and a subset $V\subseteq X$ is open if and only if $q^{-1}(V)$ is open in $M$. No separation axiom is imposed on $X$.
--
--   **Statement.** A topological space $X$ is sequential if and only if there exist a metrizable, locally compact topological space $M$ and a quotient map
--   $$q:M\longrightarrow X.$$
--
--   For a sequential space $X$ one can take for $M$ a disjoint union of copies of the convergent sequence $\mathbf{N}\cup\{\infty\}$ (the one-point compactification of the discrete space $\mathbf{N}$), one copy for each pair $(s,x)$ consisting of a sequence $s=(s_n)$ in $X$ and a limit $x$ of $s$, with $q(n)=s_n$ and $q(\infty)=x$ on that copy. Conversely every quotient of a metrizable (more generally of a first-countable, or of a sequential) space is sequential. In the paper the result explains why sequential spaces, in particular first-countable spaces, are compactly generated (Proposition E.1.2.21 and Remark E.1.2.22).
--
--   **Deviation from the source.** The paper recalls, with a reference to Franklin, only that every sequential space receives a quotient map from a first-countable space, and Remark E.1.2.22 constructs a quotient map from a locally compact Hausdorff space, namely the disjoint union above, which is metrizable; the Lean statement records this stronger classical form (metrizable spaces are first-countable and Hausdorff). Remark E.1.2.22 indexes the copies of $\mathbf{N}\cup\{\infty\}$ by the convergent sequences and sends $\infty$ to *a choice* of limit; when $X$ is not Hausdorff limits are not unique, and an arbitrary choice of one limit per sequence need not give a quotient map, whereas indexing the copies by the pairs (sequence, limit) always does.
--
--   **Formalization Note.** `SequentialSpace X` is Mathlib's class; the existential quantifies over a type `M` in the universe of `X` together with a topology and the properties `TopologicalSpace.MetrizableSpace M`, `LocallyCompactSpace M`. `Topology.IsQuotientMap` includes surjectivity. Mathlib has the direction "a quotient of a sequential space is sequential" (`Topology.IsQuotientMap.sequentialSpace`) but not the converse.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 843 (recall before Proposition E.1.2.21) and p. 844, Remark E.1.2.22; classical reference (as cited by the paper): S. P. Franklin, Spaces in which sequences suffice, Fundamenta Mathematicae 57 (1965), 107-115, Cor. 1.14

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGSpace

theorem sequentialSpace_iff_exists_isQuotientMap_metrizable
    (X : Type u) [TopologicalSpace X] :
    SequentialSpace X ↔
      ∃ (M : Type u) (_ : TopologicalSpace M) (_ : MetrizableSpace M)
        (_ : LocallyCompactSpace M) (q : M → X), IsQuotientMap q := by sorry

end CGSpace
