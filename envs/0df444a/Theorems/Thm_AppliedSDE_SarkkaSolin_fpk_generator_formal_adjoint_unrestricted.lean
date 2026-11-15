-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_generator_formal_adjoint_unrestricted
-- name    : AppliedSDE.SarkkaSolin.fpk_generator_formal_adjoint_unrestricted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:42:57.387061+00:00
-- url     : https://prove2.me/theorems/3cf85f93-34ad-43eb-8460-3d0a519f8773
-- title:
--   One-dimensional Fokker Planck formal adjoint without diffusion nonnegativity
-- statement:
--   Original adjoint 58d33226-7e65-415f-bf58-71b16064bec0 has an unused nonnegative-a hypothesis. This stronger version eliminates that hypothesis, which is absent from forward Dynkin parent 1c90076d-c7cf-45ba-9055-0b4922829eb2.
-- source:
--   Sarkka and Solin 2019, Fokker Planck Chapter 5; parent 1c90076d-c7cf-45ba-9055-0b4922829eb2.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.fpk_generator_formal_adjoint_unrestricted
    (f a p φ : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (ha : ContDiff ℝ 2 a)
    (hp : ContDiff ℝ 2 p) (hφ : ContDiff ℝ 2 φ)
    (hφcompact : HasCompactSupport φ)
    :
    (∫ x : ℝ, φ x *
      (-deriv (fun y : ℝ => f y * p y) x +
        (1 / 2 : ℝ) *
          deriv (fun y : ℝ => deriv (fun z : ℝ => a z * p z) y) x)) =
    ∫ x : ℝ,
      (f x * deriv φ x +
        a x / 2 * deriv (fun y : ℝ => deriv φ y) x) * p x := by
  sorry
