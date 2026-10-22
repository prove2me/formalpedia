-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_jump_drift_secant_bound
-- name    : AvramDividend.Classical.gaussian_esscher_jump_drift_secant_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:09:58.417457+00:00
-- url     : https://prove2.me/theorems/11b33c66-7be1-4001-88c3-06329435f092
-- title:
--   Compensated jump drift dominates its exponential secant
-- statement:
--   For arbitrary real Esscher shift φ, jump magnitude z and truncation value k, the exponential compensator exp(-φz)-1+φk is bounded above by φ times its corrected drift k-z exp(-φz). The inequality follows from exponential convexity. Integrating it under the already established Lévy integrability hypotheses controls the tilted drift by the exponent's secant slope. It may remove an explicit drift-sign assumption from the Gaussian positive-resolvent theorem when φ is a positive q-root.
-- source:
--   Convexity inequality Real.add_one_le_exp and Proved Gaussian compensated jump integrability results.

import Mathlib

theorem AvramDividend.Classical.gaussian_esscher_jump_drift_secant_bound (φ z k : ℝ) :
    Real.exp (-φ * z) - 1 + φ * k ≤
      φ * (k - z * Real.exp (-φ * z)) := by sorry
