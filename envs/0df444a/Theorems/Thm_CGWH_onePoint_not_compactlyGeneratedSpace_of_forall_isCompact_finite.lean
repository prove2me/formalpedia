-- Prove2me | Theorems.Thm_CGWH_onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite
-- name    : CGWH.onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:45.574252+00:00
-- url     : https://prove2.me/theorems/e6646b68-69d5-452e-a28a-5239d49fc525
-- title:
--   The one-point compactification of a non-discrete $T_1$ space with only finite compact subsets is compact but not compactly generated
-- statement:
--   A family of counter-examples separating compact generation from Kelley compact generation.
--
--   Conventions. A topological space $X$ is *compactly generated* if a subset $U\subseteq X$ is open as soon as $g^{-1}(U)$ is open in $K$ for every compact Hausdorff space $K$ and every continuous map $g:K\to X$. It is *Kelley compactly generated* if a subset $U\subseteq X$ is open as soon as $U\cap K$ is open in $K$ for every compact subspace $K\subseteq X$. Every compactly generated space is Kelley compactly generated, and every compact space is Kelley compactly generated. For a topological space $Y$, the *one-point compactification* $Y^+=Y\sqcup\{\infty\}$ has as open sets the open subsets of $Y$ and the complements in $Y^+$ of the closed compact subsets of $Y$; it is a compact space containing $Y$ as an open subspace.
--
--   **Statement.** Let $Y$ be a topological space such that
--
--   1. $Y$ is $T_1$,
--   2. every compact subset of $Y$ is finite,
--   3. $Y$ is not discrete.
--
--   Then:
--
--   * the one-point compactification $X:=Y^+$ is not compactly generated (although it is compact, hence Kelley compactly generated);
--   * the open subspace $Y$ of $X$ is not Kelley compactly generated.
--
--   Such spaces $Y$ exist: for instance an uncountable set with the cocountable topology (closed sets: the countable subsets and the whole set); the source refers to Steen-Seebach, *Counterexamples in Topology*, Part II, 25 and 26 (the latter is the Arens-Fort space) for examples. Hence a Kelley compactly generated space need not be compactly generated (Lemma E.2.4.11 of the source), and an open subspace of a Kelley compactly generated space need not be Kelley compactly generated (Lemma E.2.4.12), whereas open subspaces of compactly generated spaces are compactly generated. This is one of the reasons for the paper's choice of the definition of compact generation by test maps from compact Hausdorff spaces.
--
--   **Formalization Note.** `Y : Type u` with `[T1Space Y]`; hypothesis 2 is `∀ K : Set Y, IsCompact K → K.Finite` (the source says "finite and discrete": a finite subspace of a $T_1$ space is discrete) and hypothesis 3 is `¬ DiscreteTopology Y`. `OnePoint Y` is Mathlib's one-point compactification, `CompactlyGeneratedSpace` is Mathlib's notion (test spaces: compact Hausdorff spaces of `Type u`) and `CompactlyCoherentSpace` is Mathlib's name for Kelley compactly generated spaces. That `OnePoint Y` is Kelley compactly generated is an instance of Mathlib (compact spaces are compactly coherent) and is not part of the formal conclusion. The file imports Mathlib only.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 867-868, Example E.2.4.10, Lemma E.2.4.11 and Lemma E.2.4.12; classical reference (as cited by the paper for examples of such spaces Y): L. A. Steen, J. A. Seebach, Jr., Counterexamples in Topology, 2nd ed., Springer-Verlag (1978), Part II, 25 and 26

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite
    (Y : Type u) [TopologicalSpace Y] [T1Space Y]
    (hfin : ∀ K : Set Y, IsCompact K → K.Finite) (hnd : ¬ DiscreteTopology Y) :
    ¬ CompactlyGeneratedSpace (OnePoint Y) ∧ ¬ CompactlyCoherentSpace Y := by sorry

end CGWH
