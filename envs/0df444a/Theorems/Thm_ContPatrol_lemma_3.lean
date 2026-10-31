-- Prove2me | Theorems.Thm_ContPatrol_lemma_3
-- name    : ContPatrol.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:42.507821+00:00
-- url     : https://prove2.me/theorems/83220322-3803-4948-b621-c61dd978cc75
-- title:
--   Lemma 3: an Eulerian tour never entering and leaving a node via paired passages
-- statement:
--   Let $Q$ be a finite connected multigraph (loops and parallel edges allowed) with at least one edge, in which every vertex has even degree. Vertices of degree $2$ are regular points, so the nodes are the vertices of degree at least $4$. Suppose that the passages at every vertex are paired. Then there is an Eulerian tour of $Q$ that
--
--   $$\text{never enters and leaves a node via paired passages.}\tag{2}$$
--
--   This refinement of Euler's theorem gives the double tours of Theorem 3: doubling every arc and pairing the two copies of each passage turns an Eulerian tour with (2) into a tour that never reverses on a non-leaf arc.
--
--   **Formalization Note** Edge lengths play no role, so the lemma is stated for the multigraph. Condition (2) is imposed only at vertices of degree other than $2$; a circle has no nodes, so for it the condition is empty.
--
--   Differences from the source:
--   - encoding: Q is a connected Eulerian network (points of degree 2 are not nodes, p.5; minimum node degree 4, p.11) → finite connected multigraph with Nonempty E and every degree even, condition (2) imposed only at vertices of degree ≠ 2; reason: Eulerian = all degrees even (p.5); a vertex of degree 2 is a regular point, so a subdivided arc and the circle (no nodes) are the same networks as in the source; (2) cannot be imposed at such a vertex, since it fails for one loop with its two passages paired
--   - encoding: passages (x, a) identified in pairs at every node → a fixed-point-free involution σ on darts with tail (σ d) = tail d; passage (x, a) = the dart along a leaving x; reason: a node of degree d has exactly d darts leaving it, a loop giving two, as the paper counts passages
--   - encoding: an Eulerian tour S of Q satisfying (2) → a closed dart walk using every edge exactly once with σ (rev w[i]) ≠ w[i+1] cyclically; reason: the tour enters head w[i] through the passage rev w[i] and leaves through w[i+1]
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Lemma 3, p.11 (proof in the Appendix, pp.30–32)

import Mathlib
import Definitions.Def_ContPatrol_Multigraph_IsPairAvoidingEulerTour

namespace ContPatrol

open Multigraph

/-- **Lemma 3** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Lemma 3, p.11; proof in the Appendix,
pp.30–32): "Suppose Q is a connected Eulerian network such that at every node the passages are
identified in pairs (they are “paired”). Then there is an Eulerian tour S of Q satisfying
S never enters and leaves a node via paired passages. (2)"

For a finite connected multigraph (loops and parallel edges allowed) with at least one edge, in
which every vertex has even degree, and for every pairing `σ` of the passages at each vertex, there
is a closed walk using every edge exactly once that never enters and leaves a node (a vertex of
degree other than 2) through two paired passages.

**Formalization Note.** Eulerian means every node has even degree (p.5). The paper's nodes exclude
points of degree 2 (p.5), and on p.11 "there are no nodes of degree 2. Thus, the minimum node degree
in our Eulerian network is 4". Vertices of degree 2 of the multigraph are regular points of Q, as
everywhere in this mission, so condition (2) is imposed only at the other vertices, whose degree is
then at least 4 (`IsPairAvoidingEulerTour`); the condition could not be imposed at degree 2 (it
fails for a single loop at a vertex of degree 2, whose two passages are paired). This keeps the
circle, which has no nodes, and the doubled network of the proof of Theorem 3, where a leaf node
becomes a regular point. A pairing at a degree-2 vertex is the one possible swap and plays no role.
Edge lengths play no role either, so the lemma is stated for the multigraph. -/
theorem lemma_3 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : Multigraph V E) (hconn : G.Connected) (heven : ∀ v, Even (G.deg v))
    (σ : E × Bool → E × Bool) (hσ : G.IsPassagePairing σ) :
    ∃ w, G.IsPairAvoidingEulerTour σ w := by sorry

end ContPatrol
