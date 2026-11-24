-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_dtv_swap_le_of_independent
-- name    : ConformalBeyondExchangeability.dtv_swap_le_of_independent
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:46:24.71657+00:00
-- url     : https://prove2.me/theorems/bcfbf775-52af-48ce-a03a-36a6080a3963
-- title:
--   Lemma 1: total variation of a swap for independent data
-- statement:
--   Let $Z_1,\dots,Z_{n+1}$ be independent random elements of $\mathcal X\times\mathbb R$ with laws $\mu_1,\dots,\mu_{n+1}$. Let $i\in\{1,\dots,n\}$, and let $Z^i$ be the sequence with $Z_i$ and $Z_{n+1}$ swapped. Then
--
--   $$\mathsf d_{\mathsf{TV}}(Z,Z^i)\le2\,\mathsf d_{\mathsf{TV}}(Z_i,Z_{n+1})-\mathsf d_{\mathsf{TV}}(Z_i,Z_{n+1})^2\le2\,\mathsf d_{\mathsf{TV}}(Z_i,Z_{n+1}).$$
--
--   For independent data, this bounds the swap distances in the coverage gap of Theorem 2 by the distances between the marginal laws of single points.
--
--   **Formalization Note** Independence is the statement that the joint law of $Z$ is the product measure $\mu_1\otimes\dots\otimes\mu_{n+1}$. The law of $Z^i$ is the image of this product under the swap of coordinates $i$ and $n+1$.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Section 1.2, Lemma 1, p. 4; proof in Appendix E.1, p. 43

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem dtv_swap_le_of_independent {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin (n + 1) → Measure (X × ℝ)) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    tvDist (Measure.pi μ) ((Measure.pi μ).map (swapData i.castSucc)) ≤
        2 * tvDist (μ i.castSucc) (μ (Fin.last n)) - tvDist (μ i.castSucc) (μ (Fin.last n)) ^ 2 ∧
      2 * tvDist (μ i.castSucc) (μ (Fin.last n)) - tvDist (μ i.castSucc) (μ (Fin.last n)) ^ 2 ≤
        2 * tvDist (μ i.castSucc) (μ (Fin.last n)) := by sorry

end ConformalBeyondExchangeability
