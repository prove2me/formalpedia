-- Prove2me | Theorems.Thm_CGSpace_cocountable_not_compactlyGenerated
-- name    : CGSpace.cocountable_not_compactlyGenerated
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:21.165835+00:00
-- url     : https://prove2.me/theorems/80c56982-85a2-433e-a35f-fcc95259a406
-- title:
--   An uncountable set with the co-countable topology is not compactly generated: its $k$-ification is discrete
-- statement:
--   The standard example of a topological space that is not compactly generated: the co-countable topology on an uncountable set.
--
--   Let $X$ be an uncountable set endowed with the *co-countable topology*: the open subsets are $\emptyset$ and the complements of countable subsets, so the closed subsets are $X$ itself and the countable subsets of $X$. Let $k(X)$ denote the set $X$ with its compactly generated topology: a subset $Z\subseteq X$ is closed in $k(X)$ if and only if $g^{-1}(Z)$ is closed in $K$ for every compact Hausdorff space $K$ and every continuous map $g:K\to X$. A space is *compactly generated* when $k(X)=X$.
--
--   **Statement.**
--
--   1. $k(X)$ is discrete, i.e. every subset of $X$ is $k$-closed;
--   2. $X$ is not compactly generated: $k(X)\neq X$ as topological spaces.
--
--   The example shows that compact generation is a non-vacuous condition on topological spaces (Example E.1.1.9 of the paper); every uncountable proper subset of $X$ is $k$-closed but not closed.
--
--   **Formalization Note.** The co-countable topology is not a Mathlib declaration; the hypothesis `h : ∀ s, IsClosed s ↔ s = Set.univ ∨ s.Countable` says that the given topology on `X` is the co-countable one (it is an equivalence, so it determines the topology). `TopologicalSpace.compactlyGenerated.{v} X = ⊥` says that the $k$-topology is the discrete topology, and `UCompactlyGeneratedSpace.{v} X` is Mathlib's "compactly generated with respect to test spaces in `CompHaus.{v}`"; the statement is made for test spaces in an arbitrary universe `v` (for `v = u` the second assertion reads `¬ CompactlyGeneratedSpace X`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 832-833, Example E.1.1.9; for the co-countable topology the paper refers to [StSe, Part II, 29, 21], i.e. L. A. Steen, J. A. Seebach, Jr., Counterexamples in Topology, 2nd ed., Springer-Verlag (1978)

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u v

namespace CGSpace

theorem cocountable_not_compactlyGenerated
    (X : Type u) [TopologicalSpace X] [Uncountable X]
    (h : ∀ s : Set X, IsClosed s ↔ s = Set.univ ∨ s.Countable) :
    TopologicalSpace.compactlyGenerated.{v} X = ⊥ ∧ ¬ UCompactlyGeneratedSpace.{v} X := by sorry

end CGSpace
