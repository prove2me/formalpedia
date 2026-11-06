-- Prove2me | Theorems.Thm_CanadaCTP_lemma_7
-- name    : CanadaCTP.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:42.496808+00:00
-- url     : https://prove2.me/theorems/81f8b1d5-9e70-4846-b7a8-fa1905316854
-- title:
--   Lemma 7 — PathExplorer is optimal for every budget
-- statement:
--   For every path $X=(X_j)_{j\in[m]}$, $m\ge0$, and every budget $b\ge0$, the coin vector $\mathrm{coin}_X(b)$ computed by PathExplorer lies in $\mathrm{COIN}$, its strategy has expected cost at most $b$, and
--   $$
--   \mathrm{arrivalProb}(\mathrm{coin}_X(b))=\mathrm{prob}_X(b),
--   $$
--   so it is an optimal PathOpt algorithm for budget $b$.
--
--   This is the hypothesis of Lemma 4, and the optimality part of Lemma 8.
--
--   Differences from the source:
--   - encoding: "correctly calculates a characterization coin_X(b) of an optimal algorithm" → peOut X b ∈ COIN, expCost of its coin policy ≤ b, arrival probability = prob_X(b); reason: the meaning of an optimal PathOpt algorithm (Definitions 1, 2, 7)
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 7, p.14; proof pp.34–38; Definition 7, p.8

import Mathlib
import Definitions.Def_CanadaCTP_PathExplorer

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 7, p.14 (proof pp.34–38): for every path (`m ≥ 0`) and every budget `b ≥ 0`,
PathExplorer computes a coin vector `coin_X(b) ∈ COIN` whose strategy has expected cost at most
`b` and arrival probability `prob_X(b)`, i.e. an optimal PathOpt algorithm. -/
theorem lemma_7 {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ) (hb : 0 ≤ b) :
    InCOIN X (peOut X b) ∧
      expCost (pathInst X) (coinPolicy X (peOut X b)) ≤ ENNReal.ofReal b ∧
      (arrProb (pathInst X) (coinPolicy X (peOut X b))).toReal = probX X b := by sorry

end CanadaCTP
