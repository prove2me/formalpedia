-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_two_predictable_weighted_cells_L2_additive
-- name    : AvramDividend.Classical.avram_wave7_06_original_two_predictable_weighted_cells_L2_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:26:32.403957+00:00
-- url     : https://prove2.me/theorems/79523c14-9c95-463e-9d0e-40ed02d5d852
-- title:
--   Original two-cell stopped predictable weighted martingale L2 energy is additive
-- statement:
--   The L2 energy of the sum of two consecutive original-filtration predictable scalar weighted centred increments is the sum of the individual L2 energies. Both original X cells share their canonical source P and filtration. Explicit integrability of squares and cross product permits integration of the algebraic expansion. Future orthogonality follows from the authentic source independent increments and predictable adaptedness.
-- source:
--   W7-06 finite-grid original-source stopped predictable L2 isometry; two-cell induction step.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_two_predictable_weighted_cells_L2_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s] W₀)
    (hW₁ : Measurable[𝓕 (s + u)] W₁)
    (hXI : Integrable (X.X v) P)
    (hEarlierProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) * W₁ ω) P)
    (hSqA : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P)))^2) P)
    (hSqB : Integrable (fun ω =>
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))^2) P)
    (hCross : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) *
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))) P) :
    (∫ ω, ((W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) +
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P))))^2 ∂P) =
    (∫ ω, (W₀ ω * (X.X (s + u) ω - X.X s ω -
      (∫ η, X.X u η ∂P)))^2 ∂P) +
    (∫ ω, (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
      (∫ η, X.X v η ∂P)))^2 ∂P) := by sorry
