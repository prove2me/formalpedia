-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_factorial_future_auto_prefix
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_factorial_future_auto_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:42:25.200275+00:00
-- url     : https://prove2.me/theorems/17fbb454-c5f8-48eb-8ed9-4d03715f45cd
-- title:
--   Original intrinsic finite-grid L2 isometry with automatic adapted prefixes
-- statement:
--   For original intrinsic finite mark-band counts on X/P/F, original factorial moments, future independence and endpoint measurability of real counts construct the past-measurable compensated-sum prefixes and imply the genuine finite-grid L2 isometry for bounded predictable coefficients. No abstract Poisson replacement.
-- source:
--   Proved original P4-G factorial-future finite grid c73f9241 and endpoint-count adaptedness fdab4d17.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_from_factorial_future
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_prefix_adapted_from_endpoint_counts

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_factorial_future_auto_prefix
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
    (hCountEndpoint : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (N i ω).toReal))
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
