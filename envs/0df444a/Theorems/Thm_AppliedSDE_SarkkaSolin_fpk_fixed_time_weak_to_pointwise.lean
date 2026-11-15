-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_fixed_time_weak_to_pointwise
-- name    : AppliedSDE.SarkkaSolin.fpk_fixed_time_weak_to_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:34:02.540246+00:00
-- url     : https://prove2.me/theorems/e3ca70d5-5894-4f8f-a06e-e1797eeadb55
-- title:
--   Fixed-time continuous Fokker Planck residual vanishes when all compact C2 tests vanish
-- statement:
--   A continuous spatial residual D + (b u) prime - one half (a u) second derivative is zero at every spatial point if its integral against every compactly supported C2 test function vanishes. This is the fixed-time fundamental lemma of calculus of variations necessary for transition-density forward Kolmogorov theorem 1c90076d-c7cf-45ba-9055-0b4922829eb2. The fixed-time formulation avoids stronger global time smoothness required by an earlier general weak-to-pointwise theorem.
-- source:
--   Sarkka and Solin 2019 Fokker Planck / fundamental lemma of calculus of variations. Parent 1c90076d-c7cf-45ba-9055-0b4922829eb2.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.fpk_fixed_time_weak_to_pointwise
    (b a u D : ℝ -> ℝ)
    (hb : ContDiff ℝ 2 b) (ha : ContDiff ℝ 2 a)
    (hu : ContDiff ℝ 2 u) (hD : Continuous D)
    (hweak : ∀ (φ : ℝ -> ℝ),
      ContDiff ℝ 2 φ -> HasCompactSupport φ ->
      (∫ x : ℝ, φ x *
        (D x + deriv (fun z => b z * u z) x -
          (1 / 2 : ℝ) *
            deriv (fun z => deriv (fun w => a w * u w) z) x)) = 0) :
    ∀ x : ℝ, D x =
      -deriv (fun z => b z * u z) x +
        (1 / 2 : ℝ) * deriv (fun z => deriv (fun w => a w * u w) z) x := by
  sorry
