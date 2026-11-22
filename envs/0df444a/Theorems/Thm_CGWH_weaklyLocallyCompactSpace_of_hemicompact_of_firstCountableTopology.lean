-- Prove2me | Theorems.Thm_CGWH_weaklyLocallyCompactSpace_of_hemicompact_of_firstCountableTopology
-- name    : CGWH.weaklyLocallyCompactSpace_of_hemicompact_of_firstCountableTopology
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:43.761223+00:00
-- url     : https://prove2.me/theorems/1b9d64ca-b695-4a9b-b9f3-f81312e763a9
-- title:
--   A hemicompact first-countable space is locally compact: every point has a compact neighbourhood
-- statement:
--   Hemicompact first-countable spaces are locally compact.
--
--   A topological space $X$ is *hemicompact* if the set of all its compact subsets, ordered by inclusion, has a countable cofinal subset: there is a countable family $\mathcal S$ of compact subsets of $X$ such that every compact subset $C\subseteq X$ is contained in some $K\in\mathcal S$. The space $X$ is *first-countable* if every point has a countable neighbourhood basis. No separation axiom is assumed.
--
--   **Statement.** Let $X$ be a hemicompact, first-countable topological space. Then every point of $X$ has a compact neighbourhood:
--   $$\forall x\in X\ \ \exists K\subseteq X\ \text{compact}:\ K\ \text{is a neighbourhood of }x .$$
--
--   If $X$ is moreover Hausdorff, it follows that every point has a neighbourhood basis of compact sets. The paper uses the statement to characterize the locally compact objects among compactly generated weakly Hausdorff spaces: a first-countable weakly Hausdorff space that is the colimit of a sequence of compact Hausdorff subspaces is hemicompact, hence locally compact (Corollary E.2.1.17).
--
--   **Deviation from the source.** The source's conclusion reads "$X$ is locally compact", and its terminology (E.0.0.1(6)) defines a locally compact space as one in which every point has a fundamental system of compact neighbourhoods. The proof in the source produces a compact neighbourhood of each point, which is the statement formalized here; for non-Hausdorff spaces the stronger conclusion is false (add to $\mathbf Q$ one point whose only neighbourhood is the whole space: the result is compact, hence hemicompact, and first-countable, but no rational has a compact neighbourhood inside a bounded open interval). For Hausdorff spaces the two notions of local compactness coincide.
--
--   **Formalization Note.** Hemicompactness is the hypothesis `h`: there is `S : Set (Set X)`, countable, consisting of compact sets, such that every compact `C : Set X` is contained in some `K ∈ S` (Mathlib has no class for hemicompact spaces). The conclusion is Mathlib's `WeaklyLocallyCompactSpace X` (every point has a compact neighbourhood); for `T2Space X` Mathlib derives `LocallyCompactSpace X` from it. `X : Type*` is universe polymorphic, and the file imports Mathlib only.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 850, Lemma E.2.1.16 (terminology on p. 824, Terminology E.0.0.1(6))

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

namespace CGWH

theorem weaklyLocallyCompactSpace_of_hemicompact_of_firstCountableTopology
    (X : Type*) [TopologicalSpace X] [FirstCountableTopology X]
    (h : ∃ S : Set (Set X), S.Countable ∧ (∀ K ∈ S, IsCompact K) ∧
      ∀ C : Set X, IsCompact C → ∃ K ∈ S, C ⊆ K) :
    WeaklyLocallyCompactSpace X := by sorry

end CGWH
