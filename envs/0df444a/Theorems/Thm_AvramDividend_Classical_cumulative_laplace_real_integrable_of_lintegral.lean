-- Prove2me | Theorems.Thm_AvramDividend_Classical_cumulative_laplace_real_integrable_of_lintegral
-- name    : AvramDividend.Classical.cumulative_laplace_real_integrable_of_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:01:31.893632+00:00
-- url     : https://prove2.me/theorems/9077fbfd-9e69-4b36-9d32-7454ef4f58bd
-- title:
--   Convert a finite ENNReal cumulative-measure Laplace integral to an integrable real CDF
-- statement:
--   Given a nonnegative measure supported on (0,∞), finite cumulative mass on bounded positive intervals, and an ENNReal Tonelli identity for exp(-θy) multiplied by ν((−∞,y]), the ordinary real exponential Laplace integral of its right-inclusive cumulative distribution is integrable and equals the finite ENNReal value converted to real. This is the analytic measure-measurability/integrability half of the accepted proof 4271de3c-ec98-44d9-ae71-5267a2edc224, independent of Lévy scale-function existence or any Gaussian assumption.
-- source:
--   Source-faithful extraction of the real cumulative measure integrability step from accepted proof of 847548b4-661a-414b-994f-5b5a7b87dbf0. It isolates a genuine measure-theoretic obligation to satisfy Prove2Me's proof-size gate.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.cumulative_laplace_real_integrable_of_lintegral
    (ν : Measure ℝ) (hSupp : ν (Iic (0 : ℝ)) = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (hCum : ∀ y : ℝ, ν (Iic y) = ν (Ioc (0 : ℝ) y))
    (θ : ℝ) (L : ℝ≥0∞) (hLfinite : L ≠ ⊤)
    (hTon : (∫⁻ y : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-(θ * y))) * ν (Iic y)) = L) :
    IntegrableOn
      (fun y : ℝ => Real.exp (-(θ * y)) *
        (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0))
      (Ioi (0 : ℝ)) ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) *
        (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)) =
      L.toReal := by sorry
