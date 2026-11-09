-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_5_5
-- name    : CommutativeRankNC.Approximation.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:38.131341+00:00
-- url     : https://prove2.me/theorems/6175f938-6606-4356-b667-cef038df637c
-- title:
--   Lemma 5.5 — Polarization rank comparison
-- statement:
--   Fix $A\in\mathcal B$, a shared rank normalization and $k\ge1$. Homogenize $J_k$ to degree $k$ in $Y=(z,x_1,\ldots,x_m)$, and form its unnormalized complete polarization in $k$ independent copies of $Y$. Then
--
--   $$\operatorname{rank}_{\mathbb Q(Y^{(1)},\ldots,Y^{(k)})}\operatorname{Pol}(\widehat J_k)\ge\operatorname{rank}_{\mathbb Q(Y)}\widehat J_k.$$
--
--   The polarization is the alternating subset sum, whose diagonal specialization is $k!\widehat J_k(Y)$. This compares ranks over the distinct fields without identifying their variables.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: the same invertible row and column transformations applied to A and all directions → Normalization data containing rational matrix units, the rank, and the diagonal identity; reason: the normalized matrices are the source objects; they are analysis data and never input advice to the headline algorithm
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: ranks over the displayed rational-function fields → matrix rank after mapping into fraction fields of the corresponding multivariate polynomial rings; reason: the variable buckets and the homogeneous matrix are constructed exactly as on pp.24–25
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 5.5, PDF/printed p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace CommutativeRankNC.Approximation

/-- Lemma 5.5, PDF/printed p.25, ranks over the two actual rational-function fields. -/
theorem lemma_5_5 {n m : ℕ} (B : Fin m → QMatrix n) (A : QMatrix n)
    (hA : A ∈ matrixSpace B) (S : Normalization A) (k : ℕ) (hk : 0 < k) :
    polynomialMatrixRank (homogenizedJ S B k) ≤
      polynomialMatrixRank (polarizedJ S B k) := by sorry

end CommutativeRankNC.Approximation
