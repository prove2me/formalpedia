-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_grid_active_count_binomial_ws01b
-- name    : AvramDividend.Classical.bv_actual_grid_active_count_binomial_ws01b
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T09:56:10.998084+00:00
-- url     : https://prove2.me/theorems/ebded8db-bbd8-4a6c-9fc4-220f56f7b51e
-- title:
--   Binomial law for the actual Lévy active-cell count on a deterministic equal-width grid
-- statement:
--   For a finite-activity bounded-variation source spectrally negative Lévy process, the number of strictly active drift-deficit increments among n deterministic equal-width cells has the binomial law. Almost-sure monotonicity of the actual drift residual guarantees each cell is either active or exactly drift-only; the accepted complete-pattern law and binary count partition sum the probabilities.
-- source:
--   This is a source-specific theorem building on canonical Proved bv_actual_levy_residual_ae_monotone_all_times f6cc1059, bv_binary_grid_count_partition_ws01b 6686b98d and bv_actual_grid_binomial_complete_pattern_mass_ws01b a734a8e5. It supplies the actual grid-count distribution necessary for the dyadic count limit; no desired exit result or auxiliary canonical model is assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_binary_grid_count_partition_ws01b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-- True finite-grid binomial count law for the actual finite-activity
bounded-variation Lévy process. This is not yet a genuine jump-count law. -/

theorem AvramDividend.Classical.bv_actual_grid_active_count_binomial_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n k : ℕ) (h : ℝ)
    (hgap : ∀ i : ℕ, i < n →
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) = h) :
    P.real {ω : Ω |
      ((Finset.range n).filter (fun i =>
        X.X (t (i + 1)) ω - X.X (t i) ω <
          X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))).card = k} =
      (Nat.choose n k : ℝ) *
        (1 - Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ k *
        (Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ (n - k) := by sorry
