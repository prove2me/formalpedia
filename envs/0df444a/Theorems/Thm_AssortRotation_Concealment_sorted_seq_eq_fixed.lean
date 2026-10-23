-- Prove2me | Theorems.Thm_AssortRotation_Concealment_sorted_seq_eq_fixed
-- name    : AssortRotation.Concealment.sorted_seq_eq_fixed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:14.555733+00:00
-- url     : https://prove2.me/theorems/4d467e52-6a0e-4db7-8274-4b5a1a6ff4db
-- title:
--   Proof of Theorem 1, p. 39 — shown in decreasing price-adjusted valuation, the sequential revenue equals the fixed revenue $R^f$
-- statement:
--   Let products $(p_1,X_1),\dots,(p_M,X_M)$ be listed so that their price-adjusted valuations are decreasing, $X_1-p_1\ge X_2-p_2\ge\cdots\ge X_M-p_M$ (an order $\sigma$ of Definition 1). The marginal utility $v$ is nonnegative and decreasing. Showing these products sequentially in this order yields exactly the fixed-assortment revenue (4):
--   $$
--   \sum_{i=1}^{M}p_i\,\mathbb 1\{v(W_{i-1})+X_i-p_i\ge0\}\;=\;\sum_{i=1}^{M}p_i\,\mathbb 1\{v(i-1)+X_i-p_i\ge 0\},
--   $$
--   where $W_{i-1}$ is the number of purchases made in the first $i-1$ periods.
--
--   In the paper's words, a consumer facing a fixed assortment buys "in the order specified by $\sigma$". This identifies the end point of the chain of interchanges in the proof of Theorem 1(a) with $R^f$.
--
--   **Formalization Note.** The statement is pathwise, for an arbitrary list of (price, shock) pairs sorted by decreasing $X-p$; ties are allowed.
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), p. 39, Proof of Theorem 1 (first paragraph); (4) p. 11; (6) p. 11

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

namespace AssortRotation.Concealment

/-- Proof of Theorem 1, p. 39: when the products are presented sequentially in a
Definition-1 order σ (decreasing price-adjusted valuation `X − p`), the consumer buys
exactly what she would buy from the fixed assortment, so the sequential revenue (6) equals
the fixed revenue (4). -/
theorem sorted_seq_eq_fixed (v : ℕ → ℝ) (hv : MarginalUtility v) (L' : List (ℝ × ℝ))
    (hL' : L'.Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1)) :
    seqRev v L' 0 = fixedRev v L' := by sorry

end AssortRotation.Concealment
