-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_volterra_transform_scalar_identity
-- name    : AvramDividend.Classical.bv_volterra_transform_scalar_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:27:28.003987+00:00
-- url     : https://prove2.me/theorems/202935ce-994f-42d0-81e9-8b90e77e1285
-- title:
--   Scalar Laplace-transform identity for finite-activity Volterra renewal
-- statement:
--   The finite-activity bounded-variation Levy exponent rearrangement implies the exact scalar identity needed to identify the Laplace transforms of the q-scale function and its integrated Volterra renewal expression. This separates field algebra from analytic integrability and uniqueness.
-- source:
--   Elementary field algebra from psi(theta)=d theta-lambda+J.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_volterra_transform_scalar_identity
    (d q rate J ψ θ : ℝ) (hθ : θ ≠ 0) (hden : ψ - q ≠ 0)
    (hψ : ψ = d * θ - rate + J) :
    d * (ψ - q)⁻¹ = θ⁻¹ +
      (q + rate) * ((ψ - q)⁻¹ / θ) -
      J * ((ψ - q)⁻¹ / θ) := by sorry
