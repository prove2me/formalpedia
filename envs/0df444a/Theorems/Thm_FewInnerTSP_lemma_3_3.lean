-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_3_3
-- name    : FewInnerTSP.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:34.697827+00:00
-- url     : https://prove2.me/theorems/147e1c0a-4d0f-4d54-b522-4ef13d47862a
-- title:
--   Lemma 3.3 (Expansion and witness preservation)
-- statement:
--   Let $P$ be $n\ge3$ points in general position with $k>0$ interior points and a counterclockwise hull order, and let $\Gamma$ be the reduced skeleton of §3 on the retained vertices $H_0$ (retained gaps optional, maximal forced hull chains replaced by mandatory edges weighted by their chain sums). For the mixed instance on $I\cup H_0$:
--
--   1. every minimum mixed Hamiltonian cycle has the same weight as every shortest Euclidean tour of $P$;
--   2. its vertex count $N_0=|I\cup H_0|$ satisfies
--   $$N_0\le k+2k^3;$$
--   3. some minimum mixed Hamiltonian cycle has all its free edges among the edges of some shortest tour of $P$.
--
--   Clause 3 is the packing-compliant witness the recursion of §5 preserves; clause 1 makes expansion of the stored chains cost-preserving.
--
--   **Formalization Note** The reduction is defined only for $k>0$. Clause 3 also gives that a minimum mixed cycle exists.
--
--   Differences from the source:
--   - reading: the lemma for the mixed instance of §3, whose construction is preceded by 'The case k = 0 is solved directly' → the hypothesis k > 0; reason: the reduction is used and defined only for k > 0
--   - encoding: the same minimum Hamiltonian-cycle weight → every minimum mixed cycle's weight equals every shortest tour's length, existence of a minimum mixed cycle following from clause 3; reason: the two minima are attained values
--   - encoding: N0, the vertex count → N0 = |I ∪ H₀|, the card of mixedVerts; reason: the page's N0 is that count
--   - encoding: free edges form a subset of an original optimal tour → the free edges of T, as unordered index pairs, are among the edges of a shortest permutation π; reason: a tour's edges are its cyclic consecutive pairs
--   - encoding: a set of points in the plane → an indexed list P : Fin n → EuclideanSpace ℝ (Fin 2), with general position over distinct indices and no separate distinctness hypothesis; reason: no three collinear forces distinct points for n ≥ 3; the Euclidean, not the sup, metric
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 3.3, p.4 (PDF p.6); proof p.5 (PDF p.7)

import Mathlib
import Definitions.Def_FewInnerTSP_MixedInstance

namespace FewInnerTSP

/-- **Lemma 3.3 (Expansion and witness preservation).** Li, Ma, Gong, *Exact Euclidean TSP with Few
Interior Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 3.3,
p.4 (PDF p.6): "The mixed instance has the same minimum Hamiltonian-cycle weight as the original Euclidean
instance. Its vertex count satisfies N0 ≤ k + 2k³. It has an optimal witness whose free edges form a subset
of an original Euclidean optimal tour."

For `n ≥ 3` general-position points with `k > 0` interior points and a counterclockwise hull order, let
`Γ = reducedSkeleton P hull` be the skeleton of §3 (retained vertices `H₀`, optional retained gaps,
mandatory suppressed chains weighted by their chain sums). Then:
1. every minimum mixed Hamiltonian cycle has the weight of every shortest tour;
2. the mixed instance has at most `k + 2k³` vertices;
3. some minimum mixed Hamiltonian cycle has all its free edges among the edges of some shortest tour.

**Formalization Note** The reduction is defined only for `k > 0` ("The case k = 0 is solved directly",
p.3). Clause 3 also gives that a minimum mixed cycle exists. -/
theorem lemma_3_3 (n : ℕ) (hn : 3 ≤ n) (P : Fin n → Pt) (hP : GeneralPos P) (h : ℕ)
    (hull : Fin h → Fin n) (hH : IsHullOrder P hull) (hk : 0 < interiorCount P) :
    (∀ (T : Finset (Edge n (retainedPos P hull).card)) (π : Equiv.Perm (Fin n)),
      IsMinMixedCycle P (reducedSkeleton P hull) T → IsShortestTour P π →
        mixedWeight P (reducedSkeleton P hull) T = tourLen P π) ∧
    (mixedVerts P (reducedSkeleton P hull)).card ≤ interiorCount P + 2 * interiorCount P ^ 3 ∧
    (∃ (T : Finset (Edge n (retainedPos P hull).card)) (π : Equiv.Perm (Fin n)),
      IsMinMixedCycle P (reducedSkeleton P hull) T ∧ IsShortestTour P π ∧
        freeEdges T ⊆ tourEdges π) := by sorry

end FewInnerTSP
