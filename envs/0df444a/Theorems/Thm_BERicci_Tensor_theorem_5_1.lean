-- Prove2me | Theorems.Thm_BERicci_Tensor_theorem_5_1
-- name    : BERicci.Tensor.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:21.507284+00:00
-- url     : https://prove2.me/theorems/2cf09e9f-b368-4bf1-90ad-a6a31d00c5d7
-- title:
--   Theorem 5.1, p. 60 — the product of two RCD(K,∞) spaces is RCD(K,∞)
-- statement:
--   Let $(X,\mathsf d_X,\mathfrak m_X)$ and $(Y,\mathsf d_Y,\mathfrak m_Y)$ be $\mathrm{RCD}(K,\infty)$ metric measure spaces (complete and separable), and let $(Z,\mathsf d,\mathfrak m)$ be their product (5.1):
--   $$Z=X\times Y,\qquad\mathsf d((x,y),(x',y'))=\sqrt{\mathsf d_X^2(x,x')+\mathsf d_Y^2(y,y')},\qquad\mathfrak m=\mathfrak m_X\times\mathfrak m_Y.$$
--   Then $(Z,\mathsf d,\mathfrak m)$ is an $\mathrm{RCD}(K,\infty)$ space as well.
--
--   This is the tensorization property of $\mathrm{RCD}(K,\infty)$, obtained without any nonbranching assumption on the factors.
--
--   **Formalization Note** $Z$ is `WithLp 2 (X × Y)`, whose metric is the $\ell^2$ product distance. The factors are assumed σ-finite (needed by Mathlib's product measure; it follows from (MD.b) on a separable space).
-- source:
--   arXiv:1209.5786v4, Theorem 5.1, p. 60; (5.1), p. 59

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Tensor_Product
open MeasureTheory Filter Topology
open scoped ENNReal

namespace BERicci.Tensor

/-- **Theorem 5.1**, p. 60. If `(X, d_X, m_X)` and `(Y, d_Y, m_Y)` are `RCD(K, ∞)` spaces, then the
product `(Z, d, m)` of (5.1) — `Z = X × Y` with the distance `√(d_X² + d_Y²)` (the metric of
`WithLp 2 (X × Y)`) and `m = m_X × m_Y` — is `RCD(K, ∞)` as well. -/
theorem theorem_5_1
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] [SecondCountableTopology Y]
    (mX : Measure X) (mY : Measure Y) [SigmaFinite mX] [SigmaFinite mY] (K : ℝ)
    (hX : BERicci.Gamma.IsRCDInfty mX K) (hY : BERicci.Gamma.IsRCDInfty mY K) :
    BERicci.Gamma.IsRCDInfty (prodMeasure mX mY) K := by sorry

end BERicci.Tensor
