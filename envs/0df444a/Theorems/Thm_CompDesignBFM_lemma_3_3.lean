-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_3_3
-- name    : CompDesignBFM.lemma_3_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T06:32:35.952264+00:00
-- url     : https://prove2.me/theorems/54e071ea-c55f-496d-8c46-ce0c257ca864
-- title:
--   Lemma 3.3 — the product bound behind the factor e
-- statement:
--   Let $x_1,\dots,x_n\in[0,1]$ satisfy $\sum_{i=1}^n x_i\le1$, and let $i'\in\arg\max_{1\le i\le n}x_i$. Then
--
--   $$\prod_{i\ne i'}(1-x_i)\ge e^{-1}.$$
--
--   Differences from the source: none.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 3.3, p.16 (PDF 18)

import Mathlib

namespace CompDesignBFM

/-- Lemma 3.3, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.16, PDF 18 (proof p.50, PDF 52). Let `x₁, …, xₙ ∈ [0, 1]` satisfy `∑ xᵢ ≤ 1`, and let
`i'` maximize `xᵢ`. Then `∏_(i ≠ i') (1 - xᵢ) ≥ e⁻¹`. -/
theorem lemma_3_3 {n : ℕ} (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hsum : ∑ i, x i ≤ 1) (i' : Fin n) (hi' : ∀ i, x i ≤ x i') :
    Real.exp (-1) ≤ ∏ i ∈ Finset.univ.erase i', (1 - x i) := by sorry

end CompDesignBFM
