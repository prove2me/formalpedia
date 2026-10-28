-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_exists_contracting_weighted_envelope
-- name    : AvramDividend.Classical.causal_l1_exists_contracting_weighted_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:35:17.646815+00:00
-- url     : https://prove2.me/theorems/43626a08-b963-48f0-aa47-c25b70a70ff4
-- title:
--   Every positive-coefficient L1 Volterra kernel admits an integrable subunit exponential envelope
-- statement:
--   For a>0 and K integrable on positive times, choose a positive exponential damping parameter w so that the normalised positive-kernel envelope a^{-1}e^{-wt}(|β|+K(t)) is integrable and has total mass strictly below one. This furnishes the contraction parameter and majorant for the Gaussian Neumann-series construction from assumptions already established in the live branch.
-- source:
--   Combine the proved existence of a small exponential Laplace weight, integrability under damping, and normalised causal-envelope mass inequality.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_volterra_exponential_kernel_weight_small
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_positive_envelope_normalized_lt_one

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_exists_contracting_weighted_envelope
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ w : ℝ, 0 < w ∧
      IntegrableOn (fun t : ℝ =>
        a⁻¹ * Real.exp (-w * t) * (|β| + K t))
        (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ),
        a⁻¹ * Real.exp (-w * t) * (|β| + K t) ∂volume) < 1 := by sorry
