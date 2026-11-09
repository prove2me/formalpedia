-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_theorem_4_2
-- name    : CommutativeRankNC.Approximation.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:35.114023+00:00
-- url     : https://prove2.me/theorems/ea0995c6-adb3-4d42-8490-7677d0871e03
-- title:
--   Theorem 4.2 — Truncated Schur rank lower bound
-- statement:
--   Let $A\in\mathcal B$ have rank $r$ and $c=\operatorname{crk}(\mathcal B)$. A rational rank normalization exists, and for every such shared normalization and every integer $k\ge1$,
--
--   $$\operatorname{rank}_{\mathbb Q(x)}J_k(A,B(x))\ge kc-(k+1)r.$$
--
--   The right-hand side is a signed integer, so negative deficits remain negative. The truncated matrix has $k(n-r)$ rows and columns; when $r=n$ it is an empty matrix. This is the complete lower bound needed by boosting.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: the same invertible row and column transformations applied to A and all directions → Normalization data containing rational matrix units, the rank, and the diagonal identity; reason: the normalized matrices are the source objects; they are analysis data and never input advice to the headline algorithm
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: the possibly negative deficit kc−(k+1)r → integer arithmetic without truncated subtraction; reason: negative deficits are legitimate source cases, not extra assumptions
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Theorem 4.2, PDF/printed p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace CommutativeRankNC.Approximation

/-- Theorem 4.2, PDF/printed p.16: signed deficit, with normalization existence
asserted rather than assumed for the unnormalized input. -/
theorem theorem_4_2 {n m : ℕ} (B : Fin m → QMatrix n) (A : QMatrix n)
    (hA : A ∈ matrixSpace B) :
    Nonempty (Normalization A) ∧ ∀ S : Normalization A, ∀ k : ℕ, 0 < k →
      (k : ℤ) * (commutativeRank B : ℤ) - ((k : ℤ)+1) * (S.r : ℤ) ≤
        ((genericJ S B k).rank : ℤ) := by sorry

end CommutativeRankNC.Approximation
