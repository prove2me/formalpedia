-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_2_1
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:10:27.205035+00:00
-- url     : https://prove2.me/theorems/b9c9f0d3-02d9-48f7-9576-9bcab6fe1529
-- title:
--   Lemma 2.1 — fractional matching initialization
-- statement:
--   For every finite simple graph $G$ with known bounds $|V(G)|\le n$ and maximum degree at most $\Delta$, one deterministic LOCAL protocol computes a fractional matching $f$ in $O(\max\{1,\log_2\Delta\})$ rounds. Every actual edge satisfies
--
--   $$\frac{1}{2\Delta}\le f_e\le1,\qquad \sum_e f_e\ge\frac{\operatorname{OPT}(G)}4.$$
--
--   For degree zero the lower bound is interpreted with denominator $2\max\{1,\Delta\}$; there are no edges to test. All vertex loads are at most one. Initially nodes know only neighbors and the common bounds, and both endpoints report the same incident value. The program and runtime constant are uniform over all graphs and identifiers.
--
--   This supplies the source's initial fractional matching, without making any rounding or potential assertion an input.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: edge assignments → real functions on unordered pairs, zero off actual edges; reason: zero extension represents exactly the source edge values
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - encoding: asymptotic base-two logarithmic bounds → uniform positive constants, natural ceiling budgets and logarithms padded to at least one; reason: only bounded-parameter conventions change; empty and degree-zero or degree-one graphs remain included
--   - generalization: unique O(log n)-bit identifiers → all injective natural-number identifiers, with one protocol and uniform time constant; reason: the initialization, gathering, coloring-based derandomization or cleanup uses only comparisons or supplied colors; polynomial-range identifiers are included
--   - encoding: lower edge bound 1/(2 Delta) → 1/(2 max(1,Delta)); reason: the denominator agrees for every graph with an edge; the source formula has no edge instance when Delta=0
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 2.1, printed p.7, PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 2.1, printed p.7 / PDF p.9; Appendix A printed p.21 / PDF p.23. -/
theorem lemma_2_1 :
    ∃ (A : Deterministic Bounds (Finset ℕ) (ℕ → ℝ)) (C : ℝ), 0 < C ∧
      (∀ k, A.program.rounds k ≤ budget C (degreeLog k.degree)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds), boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Function.Injective ids →
          ∃ f : Sym2 (Fin N) → ℝ,
            ReportsWeights G ids (execute A G k ids (neighborIDs G ids)) f ∧
            fractional G f ∧
            (∀ e ∈ G.edgeSet, 1 / (2 * (max 1 k.degree : ℕ) : ℝ) ≤ f e ∧ f e ≤ 1) ∧
            (optimum G : ℝ) / 4 ≤ totalWeight G f := by sorry

end FasterDistributedMatching.ApproximateMatching
