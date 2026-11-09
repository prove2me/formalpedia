-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_greedy_predecessors
-- name    : ChenCapacityTerminals.Exact.greedy_predecessors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:08.865362+00:00
-- url     : https://prove2.me/theorems/7dcdb2c7-a460-43dc-8386-afe0eb97c421
-- title:
--   Lemma 2.2 — Greedy common predecessors
-- statement:
--   Let $G$ be a prepared rooted orientation on $n\ge2$ vertices with $m$ positive coalesced arcs, let $1\le d\le n$ and let $L>0$ be rational. In any legal construction, let $D$ be its greedy common-predecessor set. There is an absolute $C>0$, independent of the instance and all legal ties, such that
--   $$|D|\le C\frac nd\log(2+m).$$
--   If $L$ is a lower bound on every nonempty rooted entering cut, every unchanged final source $A$ excluding the root satisfies
--   $$w(D\setminus A,A)\ge\frac{3L}{4d}.$$
--   This is the capacity guarantee needed for unchanged sources of the final condensation. Empty group families select no vertex.
--
--   Differences from the source:
--   - generalization: the original integer-capacity graph in the paper’s setting → the structural inequality also permits finite nonnegative real capacities; reason: the cited capacity-charging argument uses only finite sums, order and the same strict threshold comparisons; integer inputs are included
--   - encoding: finite vertex labels and original arc identities → canonical labels 0,...,n-1 for machine inputs, arbitrary finite natural labels for structural statements, and ordered arc records; reason: finite relabeling preserves every instance; arc positions preserve multiplicities
--   - encoding: L ≤ λ for the rooted minimum λ → every nonempty root-avoiding shore has entering capacity at least L; reason: this is the same lower-bound assertion without choosing an optimizer or taking a default-valued infimum
--   - encoding: the legal SCC, cover and guide choices in Sections 2.1–2.3 → LegalConstruction records the full recipe including a postorder extension for arbitrary masses; reason: every legal guide has this extension; no size, expansion or time conclusion is assumed
--   - encoding: O and soft-O resource guarantees → positive constants and logarithm exponents quantified before the instances; actual finite-program executions and network traces; reason: uniform constants replace asymptotic notation without fixing an unsupported numeral or granting free graph operations
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 4, PDF p. 5, Lemma 2.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=5

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

theorem greedy_predecessors :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
      (c : Construction), Prepared G r → 1 ≤ d → d ≤ G.vertices.card → 0 < L →
      LegalConstruction G r d L b t c →
      (c.greedy.toFinset.card : ℝ) ≤
        C * ((G.vertices.card : ℝ) / d) * Real.log (2 + (G.arcs.length : ℝ)) ∧
      (RootLowerBound G r L → ∀ A ∈ unchangedSources G r ((L : ℝ) / (4 * d))
          (c.partitions (c.rounds - 1)),
        3 * (L : ℝ) / (4 * d) ≤ weight G (c.greedy.toFinset \ A) A) := by sorry

end ChenCapacityTerminals.Exact
