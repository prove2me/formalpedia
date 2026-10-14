-- Prove2me | Theorems.Thm_CauchyRiemannIndex_finiteDimensional_ker_isClosed_range_of_estimate
-- name    : CauchyRiemannIndex.finiteDimensional_ker_isClosed_range_of_estimate
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:01:38.356875+00:00
-- url     : https://prove2.me/theorems/98a6da73-a5ad-4ab9-936a-20bcdc461d9e
-- title:
--   An estimate modulo a compact operator gives finite-dimensional kernel and closed range
-- statement:
--   Let $X$, $Y$, $Z$ be real Banach spaces, $T:X\to Y$ a bounded linear operator, $K:X\to Z$ a compact linear operator, and $c$ a constant such that
--   $$\|x\|_X\le c\,\|Tx\|_Y+c\,\|Kx\|_Z\qquad\text{for all }x\in X .$$
--   Then $\ker T$ is finite-dimensional and the range of $T$ is closed.
--
--   **Formalization Note** $T$ and $K$ are continuous linear maps `X →L[ℝ] Y`, `X →L[ℝ] Z`; compactness is `IsCompactOperator K`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Lemma 4.12, p. 73

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lemma 4.12 (p. 73): let `X`, `Y`, `Z` be Banach spaces, `T : X → Y` bounded,
`K : X → Z` compact, and `‖x‖ ≤ c ‖T x‖ + c ‖K x‖` for all `x`. Then `ker T` is
finite-dimensional and `im T` is closed. -/
theorem finiteDimensional_ker_isClosed_range_of_estimate {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (T : X →L[ℝ] Y) (K : X →L[ℝ] Z) (hK : IsCompactOperator K) (c : ℝ)
    (hc : ∀ x, ‖x‖ ≤ c * ‖T x‖ + c * ‖K x‖) :
    FiniteDimensional ℝ (LinearMap.ker (T : X →ₗ[ℝ] Y)) ∧ IsClosed (Set.range T) := by
  sorry

end CauchyRiemannIndex
