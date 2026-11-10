-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_2
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:11:55.043458+00:00
-- url     : https://prove2.me/theorems/b394e9ff-a8d7-4490-a686-da1409e97e43
-- title:
--   Lemma 3.2 — short blocks
-- statement:
--   For the degree-two graph $H$ formed by locally pairing active incident edges, and every integer $\ell\ge2$, each path or cycle component with at least $\ell$ copies is partitioned into connected disjoint blocks with internal leaders and
--
--   $$\ell\le |B|\le65\ell+1.$$
--
--   Shorter components receive no blocks. One deterministic construction takes $O(\ell\max\{1,\log^*n\})$ physical LOCAL rounds. A second, when given colors from a palette of size $\zeta$ that distinguish copies at $H$-distance at most $64\ell$, takes $O(\ell(1+\max\{1,\log^*\zeta\}))$ physical rounds. Both time bounds have uniform constants. Processor inputs contain only own groups, incident values and optional own-copy colors, together with the common parameters and physical neighbor identifiers.
--
--   This retains both construction alternatives and the exact upper block size. Multiple copies of one physical creator may lie in the same block.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: edge assignments → real functions on unordered pairs, zero off actual edges; reason: zero extension represents exactly the source edge values
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - encoding: asymptotic base-two logarithmic bounds → uniform positive constants, natural ceiling budgets and logarithms padded to at least one; reason: only bounded-parameter conventions change; empty and degree-zero or degree-one graphs remain included
--   - encoding: unique O(log n)-bit identifiers → every injection below max(2,n)^(b+1), for each fixed natural b; reason: the protocol and constants may depend on the fixed ID convention, and never on a graph, its identifiers or epsilon
--   - generalization: virtual graphs arising in the bipartite matching section → locally paired active edges of an arbitrary finite simple graph; reason: the block, cut expectation and cut derandomization statements use degree at most two and local creator counts, not the parity of cycles; bipartite stages are included
--   - generalization: positive active values during a rounding stage → any real active level and incident values satisfying the same pairing partition; reason: block construction uses only the resulting degree-two topology; all source stages satisfy the predicate
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.2, printed p.8, PDF p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 3.2, printed p.8 / PDF p.10 and Appendix A. Both runtime alternatives
are part of this one item. No blocks are output on a component shorter than ell. -/
theorem lemma_3_2 :
    ∀ b : ℕ, ∃ (A0 A1 : Deterministic StageParameters StageInput (ℕ → Option Key)) (C : ℝ),
      0 < C ∧
      (∀ k, 2 ≤ k.ell → A0.program.rounds k ≤ budget C (k.ell * (logStar k.n : ℝ))) ∧
      (∀ k, 2 ≤ k.ell → A1.program.rounds k ≤ budget C (k.ell * (1 + (logStar k.zeta : ℝ)))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : StageParameters),
        2 ≤ k.ell → boundedGraph G k.n k.degree →
        ∀ (x : Sym2 (Fin N) → ℝ) (p : Pairing N), ValidPairing G x k.q p →
          ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
            (∃ B : BlockAssignment p, ValidBlocks k.ell B ∧
              ReportsBlocks ids (execute A0 G k ids
                (stageInput G ids x p none none (fun _ => false) (fun _ => none))) B) ∧
            ∀ col : Copy p → ℕ, Separates (virtualGraph p) (64 * k.ell) k.zeta col →
              ∃ B : BlockAssignment p, ValidBlocks k.ell B ∧
                ReportsBlocks ids (execute A1 G k ids
                  (stageInput G ids x p none (some col) (fun _ => false) (fun _ => none))) B := by sorry

end FasterDistributedMatching.ApproximateMatching
