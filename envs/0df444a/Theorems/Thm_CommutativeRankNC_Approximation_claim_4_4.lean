-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_claim_4_4
-- name    : CommutativeRankNC.Approximation.claim_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:46.336411+00:00
-- url     : https://prove2.me/theorems/d80a395a-c941-464d-b2ed-e5ad750d45b1
-- title:
--   Claim 4.4 — Smith exponent budget
-- statement:
--   Take $A\in\mathcal B$ of rank $r$ and any shared normalization of $A$ and the generators, and let $c=\operatorname{crk}(\mathcal B)$ and $\delta=c-r$. The actual matrix $H(t,x)$ over $K[[t]]$ has a Smith decomposition with exactly $\delta$ nonzero invariant factors. For every such ordered decomposition,
--
--   $$\sum_{i=1}^{\delta}\nu_i\le r.$$
--
--   The exponents are linked by an equality $UHV=\operatorname{diag}(t^{\nu_i},0)$ to the actual series, with $U,V$ units over $K[[t]]$. The empty sum when $\delta=0$ is zero. No valuation budget or rank-increment lemma is assumed.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: the same invertible row and column transformations applied to A and all directions → Normalization data containing rational matrix units, the rank, and the diagonal identity; reason: the normalized matrices are the source objects; they are analysis data and never input advice to the headline algorithm
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: the Smith form introduced before Claim 4.4 → existence of that form and the budget for every actual decomposition; reason: this makes the construction and nonvacuity explicit; it does not quantify over an unrelated list of integers
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Claim 4.4, PDF/printed p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace CommutativeRankNC.Approximation

/-- Claim 4.4, PDF/printed p.17, proof pp.18–20: existence of actual Smith
data, and the valuation budget for every such decomposition of the actual H. -/
theorem claim_4_4 {n m : ℕ} (B : Fin m → QMatrix n) (A : QMatrix n)
    (hA : A ∈ matrixSpace B) (S : Normalization A) :
    (∃ (ν : Fin (commutativeRank B - S.r) → ℕ)
      (U V : (Matrix (Fin (n-S.r)) (Fin (n-S.r))
        (PowerSeries (RationalFunctions m)))ˣ),
      IsSmithDecomposition (schurSeries S B) ν U V) ∧
    ∀ (ν : Fin (commutativeRank B - S.r) → ℕ)
      (U V : (Matrix (Fin (n-S.r)) (Fin (n-S.r))
        (PowerSeries (RationalFunctions m)))ˣ),
      IsSmithDecomposition (schurSeries S B) ν U V → ∑ i, ν i ≤ S.r := by sorry

end CommutativeRankNC.Approximation
