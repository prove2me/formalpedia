-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval
-- name    : AvramDividend.Classical.derivative_abs_le_on_compact_interior_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:56:28.039985+00:00
-- url     : https://prove2.me/theorems/98c2c058-e613-4558-8ab5-aa80e20cbf55
-- title:
--   Uniform derivative bound on a compact interval strictly inside the smooth HJB region
-- statement:
--   Under the C1 smoothness assumed in bounded-variation HJB verification, the derivative of the test function is continuous on the open verification region. It is therefore uniformly bounded on each nonempty compact interval strictly inside that region. This is a deterministic domination bound used when localising the finite-variation chain rule and drift compensation before stopping.
-- source:
--   Mathlib ContDiffOn.continuousOn_deriv_of_isOpen together with compact extreme value theorem; standard localised stochastic verification.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

open Set

theorem AvramDividend.Classical.derivative_abs_le_on_compact_interior_interval
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ y : ℝ, u ≤ y → y ≤ v → |deriv w y| ≤ M := by sorry
