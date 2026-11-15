-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_compact_drift_adjoint_integral
-- name    : AppliedSDE.SarkkaSolin.fpk_compact_drift_adjoint_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:29:35.119303+00:00
-- url     : https://prove2.me/theorems/afaf9910-6455-47f0-9f2c-ba4359a451d7
-- title:
--   Compact drift probability-flux integration by parts
-- statement:
--   Direct necessary child of Fokker Planck formal adjoint theorem 58d33226-7e65-415f-bf58-71b16064bec0: Compact drift probability-flux integration by parts. Derived using general compact global integration by parts. All assumptions C2 and compact support are inherited from the parent.
-- source:
--   Sarkka and Solin (2019) Chapter 5 Fokker Planck adjoint. Parent 58d33226-7e65-415f-bf58-71b16064bec0.

import Mathlib
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.fpk_compact_drift_adjoint_integral
    (f p φ : ℝ -> ℝ)
    (hf : ContDiff ℝ 2 f) (hp : ContDiff ℝ 2 p)
    (hφ : ContDiff ℝ 2 φ)
    (hφcompact : HasCompactSupport φ) :
    (∫ z : ℝ, φ z * -deriv (fun w => f w * p w) z) =
      (∫ z : ℝ, f z * deriv φ z * p z) := by
  sorry
