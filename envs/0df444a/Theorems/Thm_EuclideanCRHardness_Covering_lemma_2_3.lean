-- Prove2me | Theorems.Thm_EuclideanCRHardness_Covering_lemma_2_3
-- name    : EuclideanCRHardness.Covering.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:19.876191+00:00
-- url     : https://prove2.me/theorems/8091fe53-72e9-4fd0-a73b-0d4bfc598c4d
-- title:
--   Lemma 2.3 — Signs of closest residuals at a deepest hole
-- statement:
--   Let $Q$ be symmetric positive definite and let $x$ maximize $d_Q$ over every real target. Then
--   $$\forall v\ne0\quad\exists z\text{ closest to }x:\quad v^TQ(x-z)<0.$$
--   For each coordinate there also exist a closest residual with positive coordinate and a closest residual with negative coordinate. The two witnesses may differ across signs and coordinates. No diagonal perturbation condition is required.
--
--   Differences from the source:
--   - encoding: finite coordinates indexed 1 through n and signs ±1 → Fin n coordinates and Bool signs (true is +1); reason: bijective finite reindexing and sign coding preserve every instance
--   - encoding: minimum and maximum in the source → real infimum and supremum together with separate attainment targets; reason: positive definiteness and invertibility imply nonempty bounded optimization sets and attained extrema; none is assumed as input data
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), Lemma 2.3, printed p. 4 / PDF p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Quadratic

namespace EuclideanCRHardness.Covering

/-- Lemma 2.3. No diagonal perturbation condition is imposed here. -/
theorem lemma_2_3 {n : ℕ} (Q : RMat n) (hQ : SPD Q)
    (x : Vec n) (hx : Maximizer Q x) :
    (∀ v : Vec n, v ≠ 0 → ∃ z : Fin n → ℤ,
      Closest Q x z ∧ bilinear Q v (residual x z) < 0) ∧
    (∀ i : Fin n,
      (∃ z : Fin n → ℤ, Closest Q x z ∧ 0 < residual x z i) ∧
      (∃ z : Fin n → ℤ, Closest Q x z ∧ residual x z i < 0)) := by sorry

end EuclideanCRHardness.Covering
