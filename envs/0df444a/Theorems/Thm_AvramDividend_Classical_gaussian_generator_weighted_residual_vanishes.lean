-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_generator_weighted_residual_vanishes
-- name    : AvramDividend.Classical.gaussian_generator_weighted_residual_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:23:24.238596+00:00
-- url     : https://prove2.me/theorems/7fe4f56c-c7fd-42b5-9a17-70eca593c217
-- title:
--   Gaussian generator weighted residual cancels after the boundary adjustment
-- statement:
--   Given the already-defined transform identities for Gaussian drift, compensated jump and scale function, plus Lévy exponent decomposition and Gaussian boundary normalisation, prove the transformed generator residual integrates to zero. This conditional lemma isolates the exact integral linearity step.
-- source:
--   Lévy–Khintchine generator Laplace transform conditional algebraic cancellation.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem gaussian_generator_weighted_residual_vanishes
    (fD fJ fW : ℝ → ℝ) (d c θ q ψ J η : ℝ)
    (hD : IntegrableOn fD (Ioi (0 : ℝ)))
    (hJ : IntegrableOn fJ (Ioi (0 : ℝ)))
    (hW : IntegrableOn fW (Ioi (0 : ℝ)))
    (hDtr : (∫ x in Ioi (0 : ℝ), fD x) =
      (d * θ ^ 2 + c * θ) * (ψ - q)⁻¹ - d * η)
    (hJtr : (∫ x in Ioi (0 : ℝ), fJ x) =
      J * (ψ - q)⁻¹)
    (hWtr : (∫ x in Ioi (0 : ℝ), fW x) = (ψ - q)⁻¹)
    (hψ : ψ = d * θ ^ 2 + c * θ + J)
    (hqψ : q < ψ) (horigin : d * η = 1) :
    (∫ x in Ioi (0 : ℝ), (fD x + fJ x - q * fW x)) = 0 := by sorry

end AvramDividend.Classical
