-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_truncation_envelope
-- name    : AvramDividend.Classical.gaussian_esscher_drift_truncation_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:26:22.053554+00:00
-- url     : https://prove2.me/theorems/c54fa9bb-68ec-46e3-8327-a7551515fb68
-- title:
--   Lévy quadratic-truncation envelope for Esscher drift correction
-- statement:
--   For positive Esscher damping φ, the truncated Lévy drift correction with k(z)=z for z≤1 and k(z)=0 for z>1 has absolute value at most (φ+φ⁻¹) min(z²,1). For small jumps, use the quadratic drift bound and positivity; for large jumps use the uniform damping bound. This is the exact pointwise domination by the Lévy integrability kernel, enabling a measure-level absolute-integrability theorem and the Esscher-shifted Lévy–Khintchine exponent.
-- source:
--   Requires independently Proved gaussian_esscher_drift_small_quadratic and gaussian_esscher_drift_large_uniform.

import Mathlib

theorem AvramDividend.Classical.gaussian_esscher_drift_truncation_envelope (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ≤
      (φ + 1 / φ) * min (z ^ 2) 1 := by sorry
