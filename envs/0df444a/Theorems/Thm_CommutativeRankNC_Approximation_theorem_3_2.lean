-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_theorem_3_2
-- name    : CommutativeRankNC.Approximation.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:28.009145+00:00
-- url     : https://prove2.me/theorems/97f146af-ea4f-4cb3-83e0-d408c01eac8f
-- title:
--   Theorem 3.2 — Scaling equivalence
-- statement:
--   For any square complex matrix tuple $D=(D_i)$, the tuple can be scaled arbitrarily close to doubly stochastic if and only if it is dimension non-decreasing:
--
--   $$\bigl[\forall\eta>0\ \exists L,R\in\mathrm{GL}_n(\mathbb C):\operatorname{ds}((LD_iR)_i)\le\eta\bigr]\quad\Longleftrightarrow\quad\bigl[\forall U\le\mathbb C^n:\dim\operatorname{span}\bigcup_iD_i(U)\ge\dim U\bigr].$$
--
--   Here $\operatorname{ds}=\|\sum_iA_iA_i^*-I\|_F^2+\|\sum_iA_i^*A_i-I\|_F^2$. No full-rank-span assumption is imposed. This equivalence is an analysis result; the algorithm need not find $L$ or $R$.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: invertible complex matrices and Frobenius squared norms → matrix units, finite subspace dimensions, and sums of complex squared norms; reason: these are the same finite-dimensional objects and both directions of the equivalence are retained
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Theorem 3.2, PDF/printed p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Scaling

namespace CommutativeRankNC.Approximation

/-- Theorem 3.2, PDF/printed p.12, both directions with no full-rank assumption. -/
theorem theorem_3_2 {n m : ℕ} (D : Fin m → CMatrix n) :
    Scalable D ↔ DimensionNondecreasing D := by sorry

end CommutativeRankNC.Approximation
