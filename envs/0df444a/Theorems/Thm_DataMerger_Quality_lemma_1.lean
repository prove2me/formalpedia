-- Prove2me | Theorems.Thm_DataMerger_Quality_lemma_1
-- name    : DataMerger.Quality.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:09.881008+00:00
-- url     : https://prove2.me/theorems/ad159701-36d0-4816-88f2-49e49c296593
-- title:
--   Lemma 1, p. 6 — data allocation and the exclusivity criterion
-- statement:
--   For any two-firm B-market equilibrium profit function $\pi(d,d')$ and a nonnegative data set size $\delta$, the independent A and the merged A–B1 choose the same exclusive or nonexclusive allocation. They choose exclusivity exactly when
--
--   $$\pi(\delta,0)+\pi(0,\delta)>2\pi(\delta,\delta).$$
--
--   This ownership-independent criterion lets the quality model determine both allocations from one comparison.
--
--   **Formalization Note** The choice is a strict test. At equality, the two branches have equal payoff; for $\delta=0$ they also produce the same allocation. The result is generic in $\pi$, as in Section 3, and has no quality-model assumptions.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), p. 6 (PDF 7), Lemma 1

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

namespace DataMerger.Quality

theorem lemma_1 (pi : ℝ → ℝ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    allocI pi δ = allocM pi δ ∧
      (ExclusiveI pi δ ↔ ExclusiveM pi δ) ∧
      (ExclusiveI pi δ ↔ 2 * pi δ δ < pi δ 0 + pi 0 δ) := by sorry

end DataMerger.Quality
