-- Prove2me | Theorems.Thm_EuclideanCRHardness_Covering_quadratic_semantics
-- name    : EuclideanCRHardness.Covering.quadratic_semantics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:05.393335+00:00
-- url     : https://prove2.me/theorems/dc008ebb-1f15-45ff-b8e6-e2b2fb2b1e08
-- title:
--   Attainment, continuity and periodicity of quadratic lattice distances
-- statement:
--   Let $Q$ be a symmetric positive-definite matrix. Every target has a closest integer vector attaining $d_Q(x)$, the function $d_Q$ is continuous and integer-periodic, its range is bounded above, and
--   $$\exists x\in[0,1]^n:\quad d_Q(x)=\mu_Q^2=\max_y d_Q(y).$$
--   The finite sign minimum defining $a_Q$ is also attained. These are the semantic facts stated before equation (2.2), including the source’s attainment assertions.
--
--   Differences from the source:
--   - encoding: finite coordinates indexed 1 through n and signs ±1 → Fin n coordinates and Bool signs (true is +1); reason: bijective finite reindexing and sign coding preserve every instance
--   - encoding: minimum and maximum in the source → real infimum and supremum together with separate attainment targets; reason: positive definiteness and invertibility imply nonempty bounded optimization sets and attained extrema; none is assumed as input data
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), §2 preamble, equations (2.1)–(2.3), printed p. 3 / PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Quadratic

namespace EuclideanCRHardness.Covering

/-- The existence and regularity assertions preceding (2.2), with attainment. -/
theorem quadratic_semantics {n : ℕ} (Q : RMat n) (hQ : SPD Q) :
    (∀ x, ∃ z : Fin n → ℤ, Closest Q x z ∧ dQ Q x = quad Q (residual x z)) ∧
    Continuous (dQ Q) ∧
    (∀ x (z : Fin n → ℤ), dQ Q (fun i => x i + (z i : ℝ)) = dQ Q x) ∧
    BddAbove (Set.range (dQ Q)) ∧
    (∃ x : Vec n, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ Maximizer Q x ∧ muQ2 Q = dQ Q x) ∧
    (∃ s : Fin n → Bool, aQ Q = (1/4 : ℝ) * quad Q (fun i => signVal (s i))) := by sorry

end EuclideanCRHardness.Covering
