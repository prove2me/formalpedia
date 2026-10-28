-- Prove2me | Theorems.Thm_FiniteEnergyPlane_monotoneOn_div_rpow_of_mul_le
-- name    : FiniteEnergyPlane.monotoneOn_div_rpow_of_mul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T22:59:47.322644+00:00
-- url     : https://prove2.me/theorems/31e9a182-1917-4a24-a1ef-033576884303
-- title:
--   Monotonicity of I(s)/s^α under the inequality α I ≤ s I′
-- statement:
--   Let $S,\alpha\in\mathbb{R}$ and let $I:\mathbb{R}\to\mathbb{R}$ be differentiable at every $s\in(0,S)$, with derivative $I'(s)$, such that
--   $$\alpha\,I(s)\le s\,I'(s)\qquad\text{for all }s\in(0,S).$$
--   Then $s\mapsto I(s)/s^{\alpha}$ is nondecreasing on $(0,S)$.
--
--   This turns a differential inequality for an energy function into a power-law bound $I(s)\le C s^{\alpha}$ on small radii.
--
--   **Formalization Note** `s ^ α` is the real power `Real.rpow`. No sign condition on `I` or `α` is assumed.
-- source:
--   Standard

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Let `I` be differentiable on `(0, S)` with `α I(s) ≤ s I'(s)` there. Then `s ↦ I(s) / s^α` is
nondecreasing on `(0, S)`. -/
theorem monotoneOn_div_rpow_of_mul_le {I I' : ℝ → ℝ} {α S : ℝ}
    (hI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hineq : ∀ s ∈ Ioo 0 S, α * I s ≤ s * I' s) :
    MonotoneOn (fun s => I s / s ^ α) (Ioo 0 S) := by
  sorry

end FiniteEnergyPlane
