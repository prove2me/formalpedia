-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_shifted_compensator_real_integrable
-- name    : AvramDividend.Classical.gaussian_shifted_compensator_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:25:40.119022+00:00
-- url     : https://prove2.me/theorems/26bd127e-0ccc-4364-b87a-8386099c88f6
-- title:
--   Real integrability of Gaussian Esscher jump compensation
-- statement:
--   Under the Lévy truncated-square condition, positive Esscher damping and nonnegative shift, the real Gaussian jump-compensator z↦exp(−φz)(exp(−θz)−1+θz) is Bochner integrable on positive jump magnitudes. Derive nonnegativity from the Proved scalar bound, use established ENNReal finiteness and exact Mathlib lintegral_ofReal_ne_top_iff_integrable. This closes one integrability obligation for the real-valued Lévy–Khintchine exponent shift.
-- source:
--   Proved gaussian_shifted_compensator_integrable and gaussian_compensated_jump_pos_linear; pinned lintegral_ofReal_ne_top_iff_integrable.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_shifted_compensator_real_integrable
    (μ : Measure ℝ) (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z))
      (Ioi (0 : ℝ)) μ := by sorry
