-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_grid_exponential_integrability
-- name    : AvramDividend.Classical.bv_actual_grid_exponential_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:57:50.326195+00:00
-- url     : https://prove2.me/theorems/0bd4a243-736e-4fb9-926f-ee258cda5946
-- title:
--   The actual BV Lévy physical drift deficit has integrable exponential mesh-cell gaps and finite mesh sum
-- statement:
--   The bounded-variation Lévy drift deficit is almost surely monotone for every time pair. Therefore on every ordered finite mesh its increments are nonnegative. The proved nonnegative exponential gap integrability package yields integrability of each cell and the weighted finite sum under an explicit a.e.-strong-measurability hypothesis. This discharges the integrability premises in the finite-mesh surviving-deficit expectation bound without assuming the Lévy process has a finite first moment.
-- source:
--   Accepted bv_drift_deficit_ae_monotone_all_times and nonnegative_deficit_mesh_integrability_package.

import Theorems.Thm_AvramDividend_Classical_nonnegative_deficit_mesh_integrability_package
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.bv_actual_grid_exponential_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (N : ℕ) (ts : ℕ → ℝ≥0) (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (a : ℝ) (ha : 0 < a)
    (hCellMeas : ∀ k : ℕ, k < N →
      AEStronglyMeasurable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) ∧
    Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P := by sorry
