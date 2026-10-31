-- Prove2me | Theorems.Thm_DuanCV_Gauss_eq17_implies_posSemidef
-- name    : DuanCV.Gauss.eq17_implies_posSemidef
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:37.284971+00:00
-- url     : https://prove2.me/theorems/6b73d4d5-2efa-4686-992a-c83476cd0e79
-- title:
--   Eq. (17) gives $M_s^{II}-I\succeq0$ (corrected: $n_i,m_i\ge1$ assumed)
-- statement:
--   Let $n_i,m_i\ge1$ and $c_i$ be reals with $|c_i|\le\sqrt{(n_i-1)(m_i-1)}$ for $i=1,2$. Then
--
--   $$M_s^{II}-I\ \succeq\ 0 .$$
--
--   This is what makes the normally ordered characteristic function (18) a Gaussian of positive semi-definite form, and hence the Fourier transform of a positive measure.
--
--   Differences from the source:
--   - correction: (17) ensures that M_s^II − I is positive semi-definite → the same conclusion under the added hypothesis 1 ≤ nᵢ, mᵢ; reason: the printed step is false for the physical covariance with n₁ = 51, n₂ = 0.5, m₁ ≈ 32.592, m₂ ≈ 0.684, c₁ ≈ 39.744, c₂ ≈ −0.397, which satisfies (17) with a negative diagonal entry in M_s^II − I; the goal is unaffected, because (16) forces cᵢ = 0 in that branch and a further local squeeze applies
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, p. 4, after Eq. (17)

import Mathlib
import Definitions.Def_DuanCV_Gauss_standardFormII

namespace DuanCV.Gauss

/-- **Inequality (17) makes `M_s^{II} - I` positive semi-definite, for `nᵢ, mᵢ ≥ 1`.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, p. 4, after Eq. (17).

**Formalization Note.** The hypothesis `nᵢ, mᵢ ≥ 1` is added. The printed step is false without it:
(17) bounds `cᵢ²` by the product `(nᵢ-1)(mᵢ-1)`, which is also nonnegative when both factors are
negative, and then `M_s^{II} - I` has a negative diagonal entry. -/
theorem eq17_implies_posSemidef (n1 n2 m1 m2 c1 c2 : ℝ)
    (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (h1 : |c1| ≤ Real.sqrt ((n1 - 1) * (m1 - 1)))
    (h2 : |c2| ≤ Real.sqrt ((n2 - 1) * (m2 - 1))) :
    (standardFormII n1 n2 m1 m2 c1 c2 - 1).PosSemidef := by sorry

end DuanCV.Gauss
