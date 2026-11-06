-- Prove2me | Theorems.Thm_CanadaCTP_lemma_6
-- name    : CanadaCTP.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:28.686338+00:00
-- url     : https://prove2.me/theorems/4621a220-2021-42b2-abc8-eb056eb5eb97
-- title:
--   Lemma 6 — threshold strategies are optimal for the budget they use
-- statement:
--   Let $X=(X_j)_{j\in[m]}$ with $m\ge1$ and $\mathrm{coin}\in\mathrm{COIN}$ with $\mathrm{expCost}(\mathrm{coin})=b\ge0$. If $\mathrm{coin}$ is a threshold strategy (Definition 9) for some $\theta\ge0$, then
--   $$
--   \mathrm{arrivalProb}(\mathrm{coin})=\mathrm{prob}_X(b).
--   $$
--
--   Lemma 7 shows that PathExplorer's output is a threshold strategy, so this lemma gives its optimality.
--
--   Differences from the source:
--   - encoding: arrivalProb(coin), expCost(coin) = b → coinArr X c and b := coinCost X c; reason: Lemma 2 (item 1) identifies the closed formulas with the semantics
--   - encoding: m ≥ 1, edges 1, …, m → X : Fin (n+1) → EdgeDist; reason: 0-based indexing
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 6, p.14; proof p.34

import Mathlib
import Definitions.Def_CanadaCTP_PathOpt

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 6, p.14 (proof p.34): a threshold strategy is optimal for the budget it uses:
if `coin ∈ COIN` is a threshold strategy (Definition 9) for some `θ ≥ 0`, then
`arrivalProb(coin) = prob_X(b)` with `b = expCost(coin)`. -/
theorem lemma_6 {n : ℕ} (X : Fin (n + 1) → EdgeDist) (c : Coin X) (θ : ℝ) (hc : InCOIN X c)
    (hθ : IsThreshold X c θ) :
    coinArr X c = probX X (coinCost X c) := by sorry

end CanadaCTP
