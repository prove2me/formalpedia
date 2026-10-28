-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_values_card_uniform_ws01b
-- name    : AvramDividend.Classical.bv_actual_aligned_dyadic_values_card_uniform_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:41:48.980148+00:00
-- url     : https://prove2.me/theorems/b93e9d7e-e1a9-42f5-968a-560566e554ab
-- title:
--   Actual finite-activity BV residual visits uniformly finitely many dyadic grid values
-- statement:
--   On a common probability-one set, a finite-activity BV Lévy drift residual is monotone at every time and has uniformly bounded strictly active cells across any aligned equally spaced dyadic grid. The number of distinct observed values at each level is therefore uniformly bounded by the active-cell count plus one. This is the original-process finite-range prerequisite for its finite-jump step-function decomposition; it does not assert PRM laws, predictable compensation or killed Dynkin.
-- source:
--   Source-specific intermediate in WS1B pure-jump proof route, using canonically Proved 467a0719-5308-4651-a9a0-d262fd794c82 and f6cc1059-e8ca-403e-8d73-71a139d3dc4c. Intended to combine with right-continuous dyadic density and the finite-set stabilisation theorem to prove that actual finite-activity residual paths have finite range, then finitely many jumps. No circular exit theorem or other workstream source assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_active_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.bv_actual_aligned_dyadic_values_card_uniform_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℕ → ℝ≥0) (T : ℝ)
    (hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hGridMono : ∀ n, Monotone (grid n))
    (hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        T / ((2 ^ n : ℕ) : ℝ))) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ,
      ((Finset.range (2 ^ n + 1)).image (fun i =>
        (grid n i : ℝ) * X.drift - X.X (grid n i) ω)).card ≤ K := by sorry
