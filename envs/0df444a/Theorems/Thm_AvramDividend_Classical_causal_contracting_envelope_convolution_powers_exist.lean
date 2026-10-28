-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_contracting_envelope_convolution_powers_exist
-- name    : AvramDividend.Classical.causal_contracting_envelope_convolution_powers_exist
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:38:06.750504+00:00
-- url     : https://prove2.me/theorems/649fda91-4010-488c-9896-8b8c43579a40
-- title:
--   Contracting Gaussian Volterra envelope admits integrable recursive convolution powers
-- statement:
--   For any positive Volterra coefficient and L1 causal kernel, select an exponentially damped drift-plus-kernel envelope of mass below one and construct all of its recursive causal convolution powers. Every power is integrable and its global mass satisfies the exact product recurrence. This packages two established prerequisites for controlling the Gaussian derivative-resolvent Neumann series.
-- source:
--   Compose the proved existence of an integrable weighted envelope of subunit mass with the proved exact L1 causal convolution-power sequence construction.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_exists_contracting_weighted_envelope
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_sequence_exists

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_contracting_envelope_convolution_powers_exist
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ (w : ℝ) (κ : ℝ → ℝ),
      0 < w ∧
      κ = (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 ∧
      ∃ F : ℕ → ℝ → ℝ,
        F 0 = κ ∧
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
            κ s * F n (x - s) ∂volume) ∧
        (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
        (∀ n : ℕ,
          (∫ x in Ioi (0 : ℝ), F (n + 1) x ∂volume) =
          (∫ x in Ioi (0 : ℝ), κ x ∂volume) *
            (∫ x in Ioi (0 : ℝ), F n x ∂volume)) := by sorry
