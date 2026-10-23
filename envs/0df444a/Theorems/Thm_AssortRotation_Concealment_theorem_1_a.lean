-- Prove2me | Theorems.Thm_AssortRotation_Concealment_theorem_1_a
-- name    : AssortRotation.Concealment.theorem_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:21.186635+00:00
-- url     : https://prove2.me/theorems/779ecf77-586c-4ded-a805-e0fc7d05dbbe
-- title:
--   Theorem 1(a), p. 15 (for every fixed assortment, as proved on p. 39) — decreasing-price sequential revenue $R\ge R^f$ pathwise
-- statement:
--   Take any fixed assortment of $M$ products with nonnegative prices and realized shocks $(p_1,X_1),\dots,(p_M,X_M)$. The marginal utility $v$ is nonnegative and decreasing. Let $R$ be the retailer's revenue when the same $M$ products are offered sequentially in decreasing order of prices, $p_1\ge p_2\ge\cdots\ge p_M$, with any order among equal prices. Let $R^f$ be the fixed-assortment revenue (4), computed along any order $\sigma$ of decreasing price-adjusted valuation (Definition 1). Then
--   $$
--   R\ \ge\ R^f .
--   $$
--
--   Applied to an optimized fixed assortment, this is part (a) of Theorem 1. The decreasing-price sequence is thus a concrete heuristic that never earns less than the fixed assortment on the same products.
--
--   **Formalization Note.** The inequality is stated for every realization, not only with probability 1. It is stated for every fixed assortment, not only an optimized one, because the proof on p. 39 never uses optimality. Both orders are arbitrary lists: any ordering consistent with decreasing prices, and any ordering consistent with decreasing price-adjusted valuations.
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), p. 15, Theorem 1(a); proof p. 39

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

namespace AssortRotation.Concealment

/-- Theorem 1(a), p. 15, for every fixed assortment (as proved on p. 39). Let `L` list the
`M` products of a fixed assortment in decreasing order of prices, `p₁ ≥ ⋯ ≥ p_M`, all
nonnegative, and let `L'` be the same products in any Definition-1 order σ (decreasing
`X − p`). Then the sequential revenue `R` of `L` is at least the fixed revenue `R^f` (4). -/
theorem theorem_1_a (v : ℕ → ℝ) (hv : MarginalUtility v) (L : List (ℝ × ℝ))
    (hp : ∀ a ∈ L, 0 ≤ a.1) (hdec : L.Pairwise (fun a b => b.1 ≤ a.1)) (L' : List (ℝ × ℝ))
    (hperm : L'.Perm L) (hσ : L'.Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1)) :
    fixedRev v L' ≤ seqRev v L 0 := by sorry

end AssortRotation.Concealment
