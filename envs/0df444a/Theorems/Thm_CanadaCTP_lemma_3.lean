-- Prove2me | Theorems.Thm_CanadaCTP_lemma_3
-- name    : CanadaCTP.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:58.497192+00:00
-- url     : https://prove2.me/theorems/66075311-c602-431a-8a08-9d2b2a3c86cd
-- title:
--   Lemma 3 — $\mathrm{prob}_X$ is concave and non-decreasing
-- statement:
--   For a path with weights $X=(X_j)_{j\in[m]}$, the function $b\mapsto\mathrm{prob}_X(b)$ is concave and non-decreasing on $[0,\infty)$.
--
--   It is the shape on which SumMaximizer's steepest ascent rests.
--
--   **Formalization Note** $\mathrm{prob}_X$ is defined on all of $\mathbb R$ and both properties are stated on $[0,\infty)$, the domain $\mathbb R_{\ge0}$ of Definition 2.
--
--   Differences from the source:
--   - encoding: prob_X : ℝ≥0 → [0,1] → probX X : ℝ → ℝ, with concavity and monotonicity on Set.Ici 0; reason: same function on the source domain
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 3, p.9; proof pp.9–10

import Mathlib
import Definitions.Def_CanadaCTP_PathOpt

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 3, p.9: `prob_X(·)` is concave and non-decreasing on `ℝ≥0`. -/
theorem lemma_3 {m : ℕ} (X : Fin m → EdgeDist) :
    ConcaveOn ℝ (Set.Ici 0) (probX X) ∧ MonotoneOn (probX X) (Set.Ici 0) := by sorry

end CanadaCTP
