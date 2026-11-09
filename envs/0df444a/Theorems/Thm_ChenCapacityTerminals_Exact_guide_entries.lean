-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_guide_entries
-- name    : ChenCapacityTerminals.Exact.guide_entries
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:23.052963+00:00
-- url     : https://prove2.me/theorems/b966fb1e-f6a6-4447-b56b-0cc72cec8f16
-- title:
--   Lemma 2.3 — Guide entries charged by capacity
-- statement:
--   Let $G$ be a prepared rooted orientation, $1\le d\le n$ and $0<L\le\lambda$, where $\lambda$ is its rooted optimum. Consider any legal guide construction stopping in round $R$. Let $X$ be any vertex set avoiding the root and the source-representative and greedy probes. With $\tau=L/(4d)$, the number of directed guide edges entering $X$ obeys
--   $$|\delta_T^-(X)|\le\left(1+\min\{R,\lfloor\log_2n\rfloor\}\right)\frac{f(X)}{\tau}.$$
--   The guide edges are virtual and carry no flow capacity. The assertion holds for all avoiding sets and all legal witnesses and ties, including the empty set.
--
--   Differences from the source:
--   - generalization: the original integer-capacity graph in the paper’s setting → the structural inequality also permits finite nonnegative real capacities; reason: the cited capacity-charging argument uses only finite sums, order and the same strict threshold comparisons; integer inputs are included
--   - encoding: finite vertex labels and original arc identities → canonical labels 0,...,n-1 for machine inputs, arbitrary finite natural labels for structural statements, and ordered arc records; reason: finite relabeling preserves every instance; arc positions preserve multiplicities
--   - encoding: L ≤ λ for the rooted minimum λ → every nonempty root-avoiding shore has entering capacity at least L; reason: this is the same lower-bound assertion without choosing an optimizer or taking a default-valued infimum
--   - encoding: the legal SCC, cover and guide choices in Sections 2.1–2.3 → LegalConstruction records the full recipe including a postorder extension for arbitrary masses; reason: every legal guide has this extension; no size, expansion or time conclusion is assumed
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 5, PDF p. 6, Lemma 2.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=6

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

theorem guide_entries (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) (X : Finset ℕ)
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (hlower : RootLowerBound G r L)
    (hc : LegalConstruction G r d L b t c)
    (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r})) :
    (guideEntries (c.guide G ((L : ℝ) / (4 * d))) X : ℝ) ≤
      (1 + (min c.rounds (Nat.log2 G.vertices.card) : ℕ)) * cut G X /
        ((L : ℝ) / (4 * d)) := by sorry

end ChenCapacityTerminals.Exact
