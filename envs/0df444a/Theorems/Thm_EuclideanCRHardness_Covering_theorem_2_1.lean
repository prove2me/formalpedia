-- Prove2me | Theorems.Thm_EuclideanCRHardness_Covering_theorem_2_1
-- name    : EuclideanCRHardness.Covering.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:16.323052+00:00
-- url     : https://prove2.me/theorems/dbfb0911-05c7-4af7-bccf-daa1017c5d2e
-- title:
--   Theorem 2.1 — Weighted localization
-- statement:
--   Let $D_i>0$ and let $Q$ be symmetric positive definite. Write $\kappa=\|D^{-1}Q-I\|_\infty<1/3$ and $S=\sum_iD_i$. Then all three conclusions hold:
--   $$d_Q(h)=a_Q,$$
--   $$\left|x_i-\tfrac12\right|\le\frac{\kappa}{1-\kappa}\quad\text{for every maximizer translated into }[0,1)^n,$$
--   $$0\le\mu_Q^2-a_Q\le S(1+\kappa)\left(\frac{\kappa}{1-\kappa}\right)^2.$$
--   The center value is exact, while the deepest-hole value may be larger by the stated error.
--
--   Differences from the source:
--   - encoding: finite coordinates indexed 1 through n and signs ±1 → Fin n coordinates and Bool signs (true is +1); reason: bijective finite reindexing and sign coding preserve every instance
--   - encoding: minimum and maximum in the source → real infimum and supremum together with separate attainment targets; reason: positive definiteness and invertibility imply nonempty bounded optimization sets and attained extrema; none is assumed as input data
--   - encoding: integer translation into [0,1)^n → coordinatewise subtraction of floor; reason: the unique half-open fundamental-cube representative
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), Theorem 2.1, printed p. 3 / PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Quadratic

namespace EuclideanCRHardness.Covering

open scoped BigOperators
/-- Theorem 2.1, all three conclusions. Fractional coordinates implement the
integer translation, and all maximizing holes are quantified. -/
theorem theorem_2_1 {n : ℕ} (D : Vec n) (Q : RMat n)
    (hD : ∀ i, 0 < D i) (hQ : SPD Q) (hk : kappa D Q < 1/3) :
    dQ Q (center n) = aQ Q ∧
    (∀ x : Vec n, Maximizer Q x → ∀ i,
      |fracVector x i - 1/2| ≤ kappa D Q/(1-kappa D Q)) ∧
    (0 ≤ muQ2 Q - aQ Q ∧
      muQ2 Q - aQ Q ≤ (∑ i, D i)*(1+kappa D Q)*(kappa D Q/(1-kappa D Q))^2) := by sorry

end EuclideanCRHardness.Covering
