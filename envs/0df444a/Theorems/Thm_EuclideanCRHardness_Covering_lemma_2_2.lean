-- Prove2me | Theorems.Thm_EuclideanCRHardness_Covering_lemma_2_2
-- name    : EuclideanCRHardness.Covering.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:13.954941+00:00
-- url     : https://prove2.me/theorems/3a2c4394-4474-4b0c-97c9-6d14bac45e97
-- title:
--   Lemma 2.2 — Closest residuals
-- statement:
--   Let $Q$ be symmetric positive definite, let all diagonal scales $D_i$ be positive, and suppose $\kappa=\|D^{-1}Q-I\|_\infty<1/3$. For every real target $x$ and every closest integer point $z$, the residual $u=x-z$ satisfies
--   $$\|u\|_\infty\le\frac{1+\kappa}{2(1-\kappa)}<1.$$
--   The bound applies to every minimizing residual, with no uniqueness assumption.
--
--   Differences from the source:
--   - encoding: finite coordinates indexed 1 through n and signs ±1 → Fin n coordinates and Bool signs (true is +1); reason: bijective finite reindexing and sign coding preserve every instance
--   - encoding: minimum and maximum in the source → real infimum and supremum together with separate attainment targets; reason: positive definiteness and invertibility imply nonempty bounded optimization sets and attained extrema; none is assumed as input data
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), Lemma 2.2, printed p. 3 / PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Quadratic

namespace EuclideanCRHardness.Covering

/-- Lemma 2.2: every closest residual, with the exact strict upper bound. -/
theorem lemma_2_2 {n : ℕ} (D : Vec n) (Q : RMat n)
    (hD : ∀ i, 0 < D i) (hQ : SPD Q) (hk : kappa D Q < 1/3)
    (x : Vec n) (z : Fin n → ℤ) (hz : Closest Q x z) :
    vecMax (residual x z) ≤ (1+kappa D Q)/(2*(1-kappa D Q)) ∧
    (1+kappa D Q)/(2*(1-kappa D Q)) < 1 := by sorry

end EuclideanCRHardness.Covering
