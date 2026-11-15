-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_compact_diffusion_adjoint_integral
-- name    : AppliedSDE.SarkkaSolin.fpk_compact_diffusion_adjoint_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:29:36.770205+00:00
-- url     : https://prove2.me/theorems/f96b02da-2d96-4ee8-9f83-63eb27e32c62
-- title:
--   Compact diffusion probability-flux second integration by parts
-- statement:
--   Direct necessary child of Fokker Planck formal adjoint theorem 58d33226-7e65-415f-bf58-71b16064bec0: Compact diffusion probability-flux second integration by parts. Derived using general compact global integration by parts. All assumptions C2 and compact support are inherited from the parent.
-- source:
--   Sarkka and Solin (2019) Chapter 5 Fokker Planck adjoint. Parent 58d33226-7e65-415f-bf58-71b16064bec0.

import Mathlib
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.fpk_compact_diffusion_adjoint_integral
    (a p φ : ℝ -> ℝ)
    (ha : ContDiff ℝ 2 a) (hp : ContDiff ℝ 2 p)
    (hφ : ContDiff ℝ 2 φ)
    (hφcompact : HasCompactSupport φ) :
    (∫ z : ℝ, φ z * (1 / 2 : ℝ) *
      deriv (fun w => deriv (fun u => a u * p u) w) z) =
      (∫ z : ℝ, a z / 2 * deriv (fun w => deriv φ w) z * p z) := by
  sorry
