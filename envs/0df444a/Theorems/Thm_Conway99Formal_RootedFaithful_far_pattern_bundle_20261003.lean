-- Prove2me | Theorems.Thm_Conway99Formal_RootedFaithful_far_pattern_bundle_20261003
-- name    : Conway99Formal.RootedFaithful.far_pattern_bundle_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:07:52.837987+00:00
-- url     : https://prove2.me/theorems/d65bff65-e2b9-48e9-9d68-81a216457803
-- title:
--   Necessary conditions for the rooted far layer
-- statement:
--   In any finite strongly regular graph with parameters $(99,14,1,2)$, fix a root $r$ and call a vertex far from $r$ when it is distinct from $r$ and not adjacent to $r$. There are exactly $84$ such vertices. Each has exactly two common neighbors with $r$; those two neighbors are nonadjacent, and the resulting pair of common neighbors determines the far vertex uniquely. Thus the actual far vertices have distinct two-neighbor patterns. This is a necessary graph-owned condition for the rooted coordinate construction. It proves injectivity of the pattern map, not its surjectivity onto all eligible labels or the full graph-to-matrix equivalence.
-- source:
--   Frozen rooted-faithful formalization: formalization/2026-10-03/rooted-faithful/FixedLabels.lean and CommonWitness.lean, source commit a45708acebe3f397faccb1b646be906f24f23ee5. This is a necessary condition in an actual SRG(99,14,1,2); the converse label bridge and all SAT completeness claims remain unproved.

import Mathlib
set_option autoImplicit false

theorem Conway99Formal.RootedFaithful.far_pattern_bundle_20261003
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (r : V) :
    ((Finset.univ \ insert r (G.neighborFinset r)).card = 84) ∧
    (∀ x, x ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      Fintype.card (G.commonNeighbors r x) = 2) ∧
    (∀ x y, x ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      y ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      G.commonNeighbors r x = G.commonNeighbors r y → x = y) ∧
    (∀ x a b, x ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      a ∈ G.commonNeighbors r x → b ∈ G.commonNeighbors r x →
      ¬ G.Adj a b) := by sorry
