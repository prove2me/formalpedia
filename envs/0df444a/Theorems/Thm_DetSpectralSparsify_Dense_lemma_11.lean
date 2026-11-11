-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_11
-- name    : DetSpectralSparsify.Dense.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:30.418204+00:00
-- url     : https://prove2.me/theorems/ac64c9a2-c1ec-482f-b8da-f4e4fdfdf21d
-- title:
--   Lemma 11 (Matching decomposition) — O(Δ#) matchings in O(m log(2Δ#)) time
-- statement:
--   There are a program and an absolute constant $C$ such that for every multigraph $G$ (without isolated vertices) the program halts and partitions the non-loop edges of $G$ into at most
--   $$C\max\{\Delta^\#,1\}$$
--   matchings, within
--   $$C\big(m\log(2\max\{\Delta^\#,1\})+1\big)$$
--   steps, where $\Delta^\#$ is the maximum combinatorial degree.
--
--   The matching partition supplies the matrices $A_i$ of the expander sparsifier, with $q=O(d)$.
--
--   **Formalization Note** The output is a label for every edge (natural cell $1+e$) and the number of matchings $t$ (natural cell $0$); the labels of non-loop edges are $<t$ and two distinct non-loop edges with the same label share no endpoint (`IsMatchingPartition`). Edge weights are present in the input and irrelevant.
--
--   Differences from the source:
--   - reading: a deterministic algorithm running in the stated time (the paper fixes no machine model) → a fixed program of the closed real RAM `Program` (natural +, truncated −; real + − × ÷ √, ℕ→ℝ cast, comparisons; no floor, real constants or oracles) halting within the stated number of steps, with natural words of O(log(input + T)) bits, input and output in the layouts `graphInput`/`decodeGraph`; reason: the paper names no model; arithmetic complexity on real weights is the natural reading, and the closed instruction set prevents a step from hiding unbounded work
--   - encoding: O(Δ#) matchings in O(m log(2Δ#)) time → at most C·max(Δ#, 1) matchings within C(m log(2 max(Δ#, 1)) + 1) steps; reason: for Δ# = 0 the source expression log(0) is undefined and there is nothing to partition; the max and the +1 only cover that case and m = 0
--   - encoding: standing convention 'we discard isolated vertices' (§2, p.5) → hypothesis `G.NoIsolated` (every vertex is an endpoint of some edge); reason: the section's standing assumption made explicit as a binder; it excludes no instance the source considers
--   - encoding: a multigraph (unweighted) → a `Multigraph` whose weights are part of the input and ignored; reason: the same edge list; the weights do not enter the statement
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.20, Lemma 11 (with Algorithm 5)

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 11 (Matching decomposition), p.20. The non-loop edges of a multigraph can be partitioned
deterministically into `O(Δ#)` matchings in `O(m log(2Δ#))` time (with `Δ#` replaced by
`max(Δ#, 1)` and an additive `O(1)`, so that the bound is meaningful when `Δ# = 0`). -/
theorem lemma_11 :
    ∃ (P : Program) (K : ℕ) (C : ℝ), 0 < C ∧
    ∀ (n : ℕ) (G : Multigraph n), G.NoIsolated →
      ∃ (T : ℕ) (s' : State), RunsWithin P K (2 + n + G.m) (graphInput G [] []) T s' ∧
        G.IsMatchingPartition (s'.nat 0) (fun e => s'.nat (1 + e.val)) ∧
        (s'.nat 0 : ℝ) ≤ C * (max G.maxCombDeg 1 : ℕ) ∧
        (T : ℝ) ≤ C * (G.m * Real.log (2 * (max G.maxCombDeg 1 : ℕ)) + 1) := by sorry

end DetSpectralSparsify.Dense
