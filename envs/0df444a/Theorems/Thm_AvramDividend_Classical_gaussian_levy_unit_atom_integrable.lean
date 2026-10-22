-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_unit_atom_integrable
-- name    : AvramDividend.Classical.gaussian_levy_unit_atom_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:51:22.919689+00:00
-- url     : https://prove2.me/theorems/92f895bd-f1f4-4060-99b8-fe242a671501
-- title:
--   Bochner integrability of the unit-magnitude Lévy truncation atom
-- statement:
--   For any positive jump magnitude measure satisfying the Lévy truncated-square integrability condition, a possible unit jump atom has finite intensity. Consequently the scalar unit-atom correction is Bochner integrable. This is needed for the exact drift correction between the classical Lévy exponent's strict truncation and the Gaussian Volterra exponent's inclusive truncation.
-- source:
--   Pinned Mathlib integrableOn_const and integrable_indicator_iff, together with the Gaussian unit-atom finiteness helper.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_levy_unit_atom_integrable (μ : Measure ℝ) (θ : ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    Integrable (({1} : Set ℝ).indicator (fun _ : ℝ => θ)) μ := by sorry
