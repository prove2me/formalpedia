-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_claim_4_3
-- name    : CommutativeRankNC.Approximation.claim_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:22.330533+00:00
-- url     : https://prove2.me/theorems/08578bd2-dccd-4bcd-a12b-a63b10443f1e
-- title:
--   Claim 4.3 — Generic affine-pencil rank
-- statement:
--   Let $\mathcal B=\operatorname{span}_{\mathbb Q}\{B_i\}$, let $c=\operatorname{crk}(\mathcal B)$, and take any $A\in\mathcal B$. With $K=\mathbb Q(x_1,\ldots,x_m)$ and a fresh variable $t$,
--
--   $$\operatorname{rank}_{K(t)}(A+tB(x))=c.$$
--
--   There is no requirement that $A$ already have maximum rank. This identifies the exact generic rank against which the truncated Schur matrices are compared.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: the iterated rational-function field K(t) → the fraction field of the polynomial ring over the actual fraction field Q(x); reason: this is the same iterated field, with rational entries embedded by the canonical algebra maps
--   - encoding: the section applies shared invertible row and column maps before the rank comparison → the rank identity is written directly for the original A and B(x); reason: the shared maps preserve both affine-pencil rank and commutative rank, so this removes a choice of coordinates without changing any instance
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Claim 4.3, PDF/printed p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace CommutativeRankNC.Approximation

/-- Claim 4.3, PDF/printed p.16, over the actual field Q(x)(t). -/
theorem claim_4_3 {n m : ℕ} (B : Fin m → QMatrix n) (A : QMatrix n)
    (hA : A ∈ matrixSpace B) :
    (affinePencil (A.map (algebraMap ℚ (RationalFunctions m))) (genericPencil B)).rank =
      commutativeRank B := by sorry

end CommutativeRankNC.Approximation
