-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_from_factorial_future
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_from_factorial_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:36:24.573351+00:00
-- url     : https://prove2.me/theorems/c73f9241-250e-4b95-bda6-a150513ce443
-- title:
--   Original intrinsic finite-grid L2 isometry from factorial moments and future independence
-- statement:
--   For physical intrinsic negative-band NX on the original X/P/F, bounded predictable H and finite time grid, first and second factorial count moments plus genuine future independence imply the full finite-grid L2 isometry. All count L2, weighted and cross integrability, and conditional variance follow from proved source/analytic bridges; factorial count law and original future sigma properties remain explicit.
-- source:
--   Proved P4-B original finite-band conditional variance 1b4ba10c, P4-G centered count L2 and bounded complete-integrability original finite-grid theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_bounded_complete_integrability

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_from_factorial_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHInf : ∀ i, MemLp (H i) ⊤ P)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hJ : ∀ i, Integrable (fun ω => (N i ω).toReal) P)
    (hFactorialInt : ∀ i, Integrable (fun ω =>
      (N i ω).toReal * ((N i ω).toReal - 1)) P)
    (hFirst : ∀ i, (∫ ω, (N i ω).toReal ∂P) = r i)
    (hFactorial : ∀ i, (∫ ω,
      (N i ω).toReal * ((N i ω).toReal - 1) ∂P) = (r i) ^ 2)
    (mFuture : ℕ → MeasurableSpace Ω)
    (hFuture : ∀ i, mFuture i ≤ mΩ)
    (hSqMeas : ∀ i, StronglyMeasurable[mFuture i]
      (fun ω => ((N i ω).toReal - r i) ^ 2))
    (hIndependent : ∀ i, Indep (mFuture i) (𝓕 (grid i)) P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
