-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_7
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:10:31.898424+00:00
-- url     : https://prove2.me/theorems/1eb58239-5bb3-4ef6-bf51-49dd7a5a6aae
-- title:
--   Lemma 3.7 — cleanup
-- statement:
--   For any nonnegative edge assignment $x'$ on a finite simple graph, delete every edge incident to a vertex with pre-cleanup load strictly greater than $1/2$, giving $x''$. Then
--
--   $$c_v(x'')\le\tfrac12\quad\text{for every }v,\qquad \Phi(x'')\ge\Phi(x').$$
--
--   One deterministic LOCAL protocol computes this exact assignment in a uniform constant number of rounds, from physical neighbor identifiers and incident edge values. Output values agree at both endpoints. The input may have loads larger than one. At load exactly $1/2$, an edge is retained unless its other endpoint has load greater than $1/2$.
--
--   This restores the load reserve for the next rounding stage without losing potential.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: edge assignments → real functions on unordered pairs, zero off actual edges; reason: zero extension represents exactly the source edge values
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - generalization: unique O(log n)-bit identifiers → all injective natural-number identifiers, with one protocol and uniform time constant; reason: the initialization, gathering, coloring-based derandomization or cleanup uses only comparisons or supplied colors; polynomial-range identifiers are included
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.7, printed p.13, PDF p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 3.7, printed p.13 / PDF p.15. Strict >1/2 threshold; raw, possibly
infeasible input assignments. No fractional-matching hypothesis is added. -/
theorem lemma_3_7 :
    ∃ (A : Deterministic Unit (Finset ℕ × (ℕ → ℝ)) (ℕ → ℝ)) (T : ℕ),
      A.program.rounds () ≤ T ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ),
        NonnegativeAssignment G x → ∀ ids : Fin N → ℕ, Function.Injective ids →
          ReportsWeights G ids (execute A G () ids (weightInput G ids x)) (cleanup G x) ∧
          NonnegativeAssignment G (cleanup G x) ∧
          (∀ v, load G (cleanup G x) v ≤ 1 / 2) ∧
          potential G x ≤ potential G (cleanup G x) := by sorry

end FasterDistributedMatching.ApproximateMatching
