-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_lemma_20
-- name    : BallPolyApprox.VertexBudget.lemma_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:45.54745+00:00
-- url     : https://prove2.me/theorems/6fe3a1bf-497e-42cd-9e61-e79dd9e97bf1
-- title:
--   Lemma 20 — $\||Y|^2-1\|_2\ge c(k-1)^{-3/2}\,|\frac1k\sum_i|v_i|^2-1|$ on a simplex
-- statement:
--   Let $Y$ be uniformly distributed on a simplex with $k\ge3$ vertices $v_1,\dots,v_k$. For an absolute constant $c>0$,
--   $$\big\||Y|^2-1\big\|_2\ge\frac{c}{(k-1)^{3/2}}\Big|\frac1k\sum_i|v_i|^2-1\Big|,$$
--   where $\|\cdot\|_2$ is the $L^2$ norm of the random variable $|Y|^2-1$.
--
--   Differences from the source:
--   - encoding: Y uniform on a simplex with k vertices → affinely independent v : Fin k → ℝ^n for any n, Y = Σ Λ_i v_i with Λ ~ Dirichlet_k(1, …, 1), ‖·‖_2 = √E[(|Y|² − 1)²]; reason: the uniform law on a nondegenerate simplex in its affine hull is this image law; the ambient dimension is left free as in the source
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Lemma 20, p. 20 (PDF 22)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Lemma 20 (p. 20, PDF 22): there is an absolute constant `c > 0` such that, for `Y` uniform on
a (nondegenerate) simplex with `k ≥ 3` vertices `v_1, …, v_k` in any Euclidean space `ℝ^n`,
`‖ |Y|² − 1 ‖_2 ≥ c/(k − 1)^{3/2} · |(1/k) Σ_i |v_i|² − 1|`, where `‖·‖_2` is the `L²` norm of the
random variable. -/
theorem lemma_20 :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 3 ≤ k → ∀ v : Fin k → Rd n, AffineIndependent ℝ v →
      c / ((k : ℝ) - 1) ^ ((3 : ℝ) / 2) * |(1 / (k : ℝ)) * ∑ i, ‖v i‖ ^ 2 - 1| ≤
        Real.sqrt (∫ y, (‖y‖ ^ 2 - 1) ^ 2 ∂simplexUniform v) := by sorry

end BallPolyApprox.VertexBudget
