-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_5
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:11:39.12738+00:00
-- url     : https://prove2.me/theorems/a1e3fe21-1ac7-4cdf-a115-b02fe30f9674
-- title:
--   Lemma 3.5 — deterministic cut placement
-- statement:
--   Let $x$ be any nonnegative edge assignment, $q>0$, and let $\ell\ge2$ be an integer. Supply the locally paired active-edge graph, its valid block partition, and reusable $\zeta$-colors distinguishing copies whose creators are within physical distance $256\ell$. A deterministic physical LOCAL protocol selects exactly one copy per block and satisfies
--
--   $$F\le\frac{8Q}{\ell^2}+72qW$$
--
--   within
--
--   $$O\!\left(\ell\big((\log_2\ell)^2+\log_2\ell\max\{1,\log^*\zeta\}+1\big)\right)$$
--
--   physical rounds, with a uniform constant. Nodes initially have only their own incident values, groups, block-leader names and copy colors. Arbitrary repeated creators and true endpoints remain in $F=2q^2\sum_v(2k_v+r_v)^2$. No fractional matching or upper load bound is assumed.
--
--   This retains the source's exact deterministic cost constants and charges block communication to the physical graph.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: edge assignments → real functions on unordered pairs, zero off actual edges; reason: zero extension represents exactly the source edge values
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - encoding: asymptotic base-two logarithmic bounds → uniform positive constants, natural ceiling budgets and logarithms padded to at least one; reason: only bounded-parameter conventions change; empty and degree-zero or degree-one graphs remain included
--   - generalization: unique O(log n)-bit identifiers → all injective natural-number identifiers, with one protocol and uniform time constant; reason: the initialization, gathering, coloring-based derandomization or cleanup uses only comparisons or supplied colors; polynomial-range identifiers are included
--   - generalization: virtual graphs arising in the bipartite matching section → locally paired active edges of an arbitrary finite simple graph; reason: the block, cut expectation and cut derandomization statements use degree at most two and local creator counts, not the parity of cycles; bipartite stages are included
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.5, printed p.11, PDF p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 3.5, printed p.11 / PDF p.13 (implementation continues p.14).
The ell factor multiplies the entire bracket. Both 8 and 72 are literal source constants. -/
theorem lemma_3_5 :
    ∃ (A : Deterministic StageParameters StageInput (ℕ → Bool)) (C : ℝ), 0 < C ∧
      (∀ k, 2 ≤ k.ell → A.program.rounds k ≤ budget C
        (k.ell * ((logTwo k.ell) ^ 2 + logTwo k.ell * (logStar k.zeta : ℝ) + 1))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : StageParameters),
        2 ≤ k.ell → 0 < k.q → boundedGraph G k.n k.degree →
        ∀ (x : Sym2 (Fin N) → ℝ), NonnegativeAssignment G x →
          ∀ (p : Pairing N), ValidPairing G x k.q p →
            ∀ (B : BlockAssignment p), ValidBlocks k.ell B →
              ∀ col : Copy p → ℕ, ReusableColors G k.ell k.zeta col →
                ∀ ids : Fin N → ℕ, Function.Injective ids →
                  ∃ s : Copy p → Copy p, ValidCuts B s ∧
                    ReportsCuts (execute A G k ids (stageInput G ids x p (some B) (some col)
                      (fun _ => false) (fun _ => none))) B s ∧
                    cutCost G x k.q B s ≤
                      8 * penalty G x / (k.ell : ℝ) ^ 2 + 72 * k.q * totalWeight G x := by sorry

end FasterDistributedMatching.ApproximateMatching
