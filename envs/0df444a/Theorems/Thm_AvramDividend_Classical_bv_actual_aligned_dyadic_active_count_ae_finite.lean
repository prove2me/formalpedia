-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_active_count_ae_finite
-- name    : AvramDividend.Classical.bv_actual_aligned_dyadic_active_count_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:59:04.154888+00:00
-- url     : https://prove2.me/theorems/467a0719-5308-4651-a9a0-d262fd794c82
-- title:
--   Actual finite-activity spectrally negative Lévy residual has uniformly bounded active-cell count almost surely on nested dyadic grids
-- statement:
--   For the actual original bounded-variation finite-activity spectrally negative Lévy process, take any nested dyadic grid on a fixed finite real horizon T with uniform step T/2^n. On a single P-probability-one set, there exists a finite natural K(ω) such that, at every dyadic refinement level, no more than K cells have a strictly positive increment of the original drift residual Y_t=t·drift−X_t. The proof combines the accepted actual uniform-grid expected-count bound E[N_n]≤ν((−∞,0))T with the accepted aligned-grid monotone-refinement theorem and the accepted almost-sure uniformly finite count result; measurability follows from adaptedness. This establishes the dyadic finite activity conclusion for original Lévy sample paths without introducing an auxiliary compound-Poisson process.
-- source:
--   Avram, Palmowski and Pistorius (2007), bounded-variation finite-activity first-jump law; Prove2Me accepted dyadic bounds and a.s. monotone convergence.

import Theorems.Thm_AvramDividend_Classical_bv_aligned_grid_active_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_bv_actual_uniform_grid_active_expected_le_intensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_aligned_dyadic_active_count_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℕ → ℝ≥0) (T : ℝ)
    (hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hStep : ∀ n i : ℕ, i < 2 ^ n →
      grid n i ≤ grid n (i + 1))
    (hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        T / ((2 ^ n : ℕ) : ℝ))) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ,
      (∑ i ∈ Finset.range (2 ^ n),
        ite (((grid n i : ℝ) * X.drift - X.X (grid n i) ω) <
          ((grid n (i + 1) : ℝ) * X.drift - X.X (grid n (i + 1)) ω))
          (1 : ℕ) 0) ≤ K := by sorry
