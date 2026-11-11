-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_lemma_7_6
-- name    : DistributedMWC440.UpperBound.lemma_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:11.62117+00:00
-- url     : https://prove2.me/theorems/5b16d430-8a24-40a8-832c-a8e1c73b9088
-- title:
--   Lemma 7.6 (Patching after capture)
-- statement:
--   Fix a captured LDD tree and the skeleton vertices of a minimum cycle. Run the doubled-graph hop-bounded computations with fresh independent fair bits on non-forest edges and zero parity on the forest. All segment, scale and capture conditions below are hypotheses; patch success is a conclusion.
--
--   Let $R=S\cap V(C^\star)$ contain at least two vertices, and suppose each $R$-segment has at most $L_{\mathrm{seg}}$ edges. Assume $k\ge1/2$, $d,\epsilon>0$, nonnegative truncated shifts, capture at $s$, and
--
--   $$
--   w(C^\star)\le2(d-2\epsilon\delta_{\max}).
--   $$
--
--   Over fresh parity bits, extended detection finds a candidate whose computed weight estimate is at most
--
--   $$
--   (1+O(\epsilon))2\delta_{\max}
--   $$
--
--   with probability at least $1/2$. The hidden constant is uniform before the graph, tree, parameters and patch-output choices. The candidate carries a genuine simple cycle.
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - generalization: outputs of the specified approximate SSSP algorithm → any selection of the specified distance and parent-tree outputs, with the measure evaluated on the resulting event; reason: the lower-bound argument holds for every permitted tree choice, including the source algorithm; intended computable selections give ordinary measurable probability events
--   - encoding: a candidate in extended detection → a simple cycle in the union of a projected odd-parity parent path and the local tree path, with the source estimate; reason: parity bits are independent on unordered non-forest edges; this retains the exact conditional probability at least one half
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Lemma 7.6, printed p. 38 / PDF p. 40.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem lemma_7_6 : ∃ c : ℝ, 0 < c ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (W : WGraph V), W.graph.Connected →
      (∀ u v, W.graph.Adj u v → 0 < W.length u v) →
    ∀ (S : Finset V) (Cstar : Cycle W), IsMinimum Cstar →
    ∀ (k d ε : ℝ), 1/2 ≤ k → 0 < d → 0 < ε →
    ∀ (δ : Shifts S), ValidShifts S k d δ →
      2 ≤ (cycleSkeleton Cstar S).card →
    ∀ L : ℕ, SegmentBound Cstar (cycleSkeleton Cstar S) L →
      Cstar.weight ≤ 2*(d-2*ε*deltaMax S k d) →
    ∀ s : S, Captures W S (cycleSkeleton Cstar S) k d δ s →
    ∀ T : LDDTree W S k d ε δ,
    ∀ patch : (χ : Parities V) → PatchOutputs T χ L,
      (1/2 : ℝ≥0∞) ≤ parityLaw
        {χ | ExtendedSuccess (patch χ) ((1+c*ε)*2*deltaMax S k d)} := by sorry

end DistributedMWC440.UpperBound
