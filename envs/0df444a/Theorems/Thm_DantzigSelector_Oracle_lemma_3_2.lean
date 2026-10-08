-- Prove2me | Theorems.Thm_DantzigSelector_Oracle_lemma_3_2
-- name    : DantzigSelector.Oracle.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:07:01.714981+00:00
-- url     : https://prove2.me/theorems/a7fdcc67-6e94-459f-a346-c1149fb7e074
-- title:
--   Lemma 3.2 — $\|X\beta\|_{\ell_2}\le\sqrt{1+\delta_{2S}}\,(\|\beta\|_{\ell_2}+(2S)^{-1/2}\|\beta\|_{\ell_1})$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ be any real matrix, $S\ge1$ an integer, and $\delta_{2S}$ the $2S$-restricted isometry constant of $X$, the smallest $\delta\ge0$ with $(1-\delta)\|c\|_{\ell_2}^2\le\|Xc\|_{\ell_2}^2\le(1+\delta)\|c\|_{\ell_2}^2$ for every $c$ supported on at most $2S$ indices. Then for every vector $\beta\in\mathbb R^p$,
--   $$\|X\beta\|_{\ell_2}\le\sqrt{1+\delta_{2S}}\,\Big(\|\beta\|_{\ell_2}+(2S)^{-1/2}\|\beta\|_{\ell_1}\Big).$$
--
--   The inequality extends the upper restricted isometry bound from sparse vectors to arbitrary ones at the cost of an $\ell_1$ term. In the proof of Theorem 1.2 it bounds $\|X\beta'\|_{\ell_2}$ for the non-sparse part $\beta'$ of the constrained thresholding decomposition.
--
--   **Formalization Note** No sparsity of $\beta$ and no column normalization is assumed: the lemma holds for every vector and every matrix. $(2S)^{-1/2}\|\beta\|_{\ell_1}$ is written $\|\beta\|_{\ell_1}/\sqrt{2S}$; the hypothesis $S\ge1$ keeps the denominator positive.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 19, Lemma 3.2

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

open CandesTao.Decoding DantzigSelector.Sparse

namespace DantzigSelector.Oracle

/-- Candès–Tao (2007), Lemma 3.2, p. 19: for every `β ∈ ℝ^p`,
`‖Xβ‖_{ℓ2} ≤ √(1 + δ_{2S}) (‖β‖_{ℓ2} + (2S)^{-1/2} ‖β‖_{ℓ1})`. -/
theorem lemma_3_2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S)
    (β : Fin p → ℝ) :
    l2Norm (X.mulVec β) ≤
      Real.sqrt (1 + restrictedIsometryConst X (2 * S)) *
        (l2Norm β + l1Norm β / Real.sqrt (2 * (S : ℝ))) := by sorry

end DantzigSelector.Oracle
