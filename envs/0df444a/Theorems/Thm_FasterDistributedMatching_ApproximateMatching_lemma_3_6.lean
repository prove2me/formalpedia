-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_6
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:11:47.148212+00:00
-- url     : https://prove2.me/theorems/eaf5a12b-4437-463f-8eb3-df27accdf859
-- title:
--   Lemma 3.6 — one rounding stage
-- statement:
--   In the bipartite stage setting with its supplied bipartition, let $x$ be a fractional matching with every physical load at most $1/2$, let $q>0$ and $\ell\ge2$, and supply the locally paired active graph, valid blocks and one cut copy in each block. One deterministic physical LOCAL procedure takes $O(\ell)$ rounds and produces a fractional matching $x'$ with loads at most one such that
--
--   $$x'_e\in\{0,2q\}\ \text{if }x_e=q,\qquad x'_e=x_e\ \text{otherwise},\qquad
--   \Phi(x')\ge\Phi(x)-F.$$
--
--   The output values agree at both endpoints. There is an edge-assignment readout at every physical round, initially equal to $x$ and finally equal to $x'$, and every such intermediate assignment is a fractional matching, with its endpoint reports agreeing. Constants are uniform over all stage data, and no coloring or global path decomposition is an input.
--
--   This is the entire rounding-stage conclusion, including unchanged inactive edges and intermediate feasibility. Its bipartite standing assumption excludes odd uncut cycles.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: edge assignments → real functions on unordered pairs, zero off actual edges; reason: zero extension represents exactly the source edge values
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - generalization: unique O(log n)-bit identifiers → all injective natural-number identifiers, with one protocol and uniform time constant; reason: the initialization, gathering, coloring-based derandomization or cleanup uses only comparisons or supplied colors; polynomial-range identifiers are included
--   - encoding: intermediate assignments have loads at most one → a fractional, endpoint-consistent trace at every physical-round readout, with initial x and final x prime; reason: the protocol can retain x while coordinating and perform the source simultaneous update at its final round
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.6, printed p.12, PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 3.6, printed p.12 / PDF p.14. This section's bipartition is retained;
odd cycles are not silently admitted. Intermediate feasibility refers to the protocol's
edge readout at every physical round, including initialization and termination. -/
theorem lemma_3_6 :
    ∃ (A : Deterministic StageParameters StageInput (ℕ → ℝ)) (C : ℝ), 0 < C ∧
      (∀ k, 2 ≤ k.ell → A.program.rounds k ≤ budget C k.ell) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : StageParameters),
        2 ≤ k.ell → 0 < k.q → boundedGraph G k.n k.degree →
        ∀ side : Fin N → Bool, Bipartition G side →
          ∀ (x : Sym2 (Fin N) → ℝ), fractional G x → (∀ v, load G x v ≤ 1 / 2) →
            ∀ p : Pairing N, ValidPairing G x k.q p →
              ∀ B : BlockAssignment p, ValidBlocks k.ell B →
                ∀ s : Copy p → Copy p, ValidCuts B s →
                  ∀ ids : Fin N → ℕ, Function.Injective ids →
                    let inp := stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v))
                    ∃ (x' : Sym2 (Fin N) → ℝ) (trace : ℕ → Sym2 (Fin N) → ℝ),
                      ReportsWeights G ids (execute A G k ids inp) x' ∧
                      fractional G x' ∧ (∀ v, load G x' v ≤ 1) ∧
                      (∀ e ∈ G.edgeSet, (x e = k.q → x' e = 0 ∨ x' e = 2 * k.q) ∧
                        (x e ≠ k.q → x' e = x e)) ∧
                      potential G x - cutCost G x k.q B s ≤ potential G x' ∧
                      trace 0 = x ∧ trace (A.program.rounds k) = x' ∧
                      ∀ t, t ≤ A.program.rounds k → fractional G (trace t) ∧
                        ReportsWeights G ids (fun v => A.program.out
                          (A.program.run G k ids inp (fun _ _ => false) t v)) (trace t) := by sorry

end FasterDistributedMatching.ApproximateMatching
