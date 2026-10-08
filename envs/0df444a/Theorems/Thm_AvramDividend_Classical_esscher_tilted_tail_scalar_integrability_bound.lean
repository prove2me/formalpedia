-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_scalar_integrability_bound
-- name    : AvramDividend.Classical.esscher_tilted_tail_scalar_integrability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:45:14.002977+00:00
-- url     : https://prove2.me/theorems/f8afe36d-0595-4838-8daa-525d87c10561
-- title:
--   Esscher-damped jump tail area is controlled by the original Lévy quadratic truncation
-- statement:
--   For a positive Esscher exponent phi and positive jump magnitude z, the product exp(-phi*z) times min(z²,z) is bounded by the original Lévy integrability kernel min(1,z²) times the finite positive constant (1+1/phi). On 0≤z≤1 this is simply exp(-phi*z)≤1; for z≥1 it follows from (phi*z)exp(-phi*z)≤1, itself a consequence of exp(u)≥u for u≥0. This is a pointwise integrable-envelope component for proving finite first moments of the Esscher-shifted descending ladder-height Lévy measure.
-- source:
--   Pinned Mathlib Real.add_one_le_exp, Real.exp_add and Real.exp_le_one_iff; original Lévy measure truncated square integrability.

import Mathlib
open Set

theorem AvramDividend.Classical.esscher_tilted_tail_scalar_integrability_bound
    (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    Real.exp (-(φ * z)) * min (z ^ 2) z ≤
      (1 + φ⁻¹) * min 1 (z ^ 2) := by sorry
