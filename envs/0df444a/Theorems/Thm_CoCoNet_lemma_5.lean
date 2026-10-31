-- Prove2me | Theorems.Thm_CoCoNet_lemma_5
-- name    : CoCoNet.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:47.337709+00:00
-- url     : https://prove2.me/theorems/65c818e5-6243-4a62-a5d7-61a1c931f0b4
-- title:
--   Lemma 5 — sign patterns of $(I-W)^{-1}$ and $L_{B,C}^{-1}(I-W)$
-- statement:
--   Let $(m,W)$ be admissible.
--   1. If $I-W$ is invertible, every entry of $(I-W)^{-1}$ is nonnegative.
--   2. For all $B,C\subseteq[n]$, the matrix $L_{B,C}^{-1}(I-W)$ has nonnegative diagonal entries and nonpositive off-diagonal entries.
--
--   These sign patterns drive Lemmas 3 and 4: moving the asset vector along $(I-W)d_X$ lowers the fair equilibrium prices of the banks outside $X$.
--
--   **Formalization Note** Part 2 is stated without the invertibility of $I-W$; $L_{B,C}$ itself is always invertible.
--
--   Differences from the source:
--   - generalization: part (b) under the lemma's hypothesis 'If I − W is invertible' → part (b) without IsUnit (1 - W); reason: L_{B,C} is invertible for every admissible network, the paper's limit argument (α → 1) does not use invertibility of I − W, and Lemma 3, posed here without Assumption 1, uses (b); the printed statement is the special case
--   - encoding: (I − W)⁻¹ and L⁻¹_{B,C} → Matrix.inv; reason: nonsingular matrices here, so Matrix.inv is the inverse
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Lemma 5, p.34

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_Lmat

namespace CoCoNet

/-- **Lemma 5 (sign patterns of `(I − W)⁻¹` and `L_{B,C}⁻¹(I − W)`).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Lemma 5, p.34: "If I − W is invertible, the matrix
(I − W)⁻¹ has only non-negative entries. Moreover, for any B, C ⊆ [n] the matrix
L⁻¹_{B,C}(I − W) has non-negative entries on the diagonal and non-positive entries otherwise."

**Formalization Note.** Part (a) assumes `IsUnit (1 - W)` (Assumption 1); part (b) is stated
without it (`L_{B,C}` is always invertible, and Lemma 3, which assumes no Assumption 1, uses (b)).
`B`, `C` are arbitrary, possibly overlapping. `⁻¹` is `Matrix.inv`. -/
theorem lemma_5 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hadm : IsAdmissible m W) :
    (IsUnit (1 - W) → ∀ i j, 0 ≤ (1 - W)⁻¹ i j) ∧
      ∀ (B C : Finset (Fin n)) (i j : Fin n),
        (i = j → 0 ≤ ((Lmat m W B C)⁻¹ * (1 - W)) i j) ∧
        (i ≠ j → ((Lmat m W B C)⁻¹ * (1 - W)) i j ≤ 0) := by sorry

end CoCoNet
