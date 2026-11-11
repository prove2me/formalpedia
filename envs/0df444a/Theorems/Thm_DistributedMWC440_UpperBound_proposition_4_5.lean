-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_proposition_4_5
-- name    : DistributedMWC440.UpperBound.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:25:48.528802+00:00
-- url     : https://prove2.me/theorems/785c346b-098e-4a3b-9fb5-983075f1ed66
-- title:
--   Proposition 4.5 (Safely capturing a cycle)
-- statement:
--   Let $C$ be a simple cycle and $R=S\cap V(C)$ contain at least two centers. Choose any nearest skeleton vertex $q$ to the capturing center. Segments are maximal cycle subpaths between consecutive skeleton vertices, and visibility is defined using the source weighted radius.
--
--   Assume $k\ge1/2$, $d>0$, $\epsilon>0$, nonnegative truncated shifts, capture at $s$, and
--
--   $$
--   w(C)\le2(d-2\epsilon\delta_{\max}),\qquad R=S\cap V(C),\qquad |R|\ge2.
--   $$
--
--   For every nearest skeleton vertex $q$, at most one segment is invisible, counted independently of its orientation. Every vertex of $C$ outside that segment's internal vertices is $\epsilon$-safe for $s$. If there is no invisible segment, all vertices are safe. In particular, $R=V(C)$ implies safety of every cycle vertex. Visibility uses the source radius $d-2\epsilon\delta_{\max}$.
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - encoding: the antipodal segment exception → uniqueness up to unordered segment edges and safety outside every invisible segment interior; reason: this unfolds the preceding visibility and antipodal definitions and retains the special case with all cycle vertices as centers
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Proposition 4.5, printed p. 18 / PDF p. 20.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem proposition_4_5 {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (hpos : ∀ u v, W.graph.Adj u v → 0 < W.length u v)
    (S : Finset V) (C : Cycle W) (k d ε : ℝ)
    (hk : 1/2 ≤ k) (hd : 0 < d) (hε : 0 < ε)
    (δ : Shifts S) (hδ : ValidShifts S k d δ)
    (hcard : 2 ≤ (cycleSkeleton C S).card)
    (hweight : C.weight ≤ 2*(d-2*ε*deltaMax S k d))
    (s : S) (hcapture : Captures W S (cycleSkeleton C S) k d δ s) :
    (∀ q ∈ cycleSkeleton C S, dist W s.val q = setDist W s.val (cycleSkeleton C S) →
      (∀ u v (P : W.graph.Walk u v), IsSegment C (cycleSkeleton C S) P →
        ¬Visible C q P (d-2*ε*deltaMax S k d) →
        ∀ u' v' (P' : W.graph.Walk u' v'), IsSegment C (cycleSkeleton C S) P' →
        ¬Visible C q P' (d-2*ε*deltaMax S k d) → P.edges.toFinset = P'.edges.toFinset) ∧
      (∀ v ∈ C.walk.support,
        (∀ a b (P : W.graph.Walk a b), IsSegment C (cycleSkeleton C S) P →
          ¬Visible C q P (d-2*ε*deltaMax S k d) → v ∉ P.support.tail.dropLast) →
        Safe W S k d ε δ s v)) ∧
    (cycleSkeleton C S = C.walk.support.toFinset →
      ∀ v ∈ C.walk.support, Safe W S k d ε δ s v) := by sorry

end DistributedMWC440.UpperBound
