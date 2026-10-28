-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:03:22.934755+00:00
-- url     : https://prove2.me/theorems/e57db112-886f-464e-be1f-8dd9bd54b7b9
-- title:
--   Strict finite-mesh Lévy drawdown/minimum symmetry from a full-vector reversal law
-- statement:
--   For a spectrally negative Lévy path and any path measure ν, if ν gives equal mass to every measurable event on n equal-mesh increments and its reversal, then the strict finite-grid terminal drawdown and running-infimum events have equal probabilities. Convert vector symmetry into an invariant pushed-forward law and use the Proved general strict prefix reversal, prefix telescoping and measurability.
-- source:
--   Proved avram_ws01e_b_general_strict_prefix_reversal_of_law and Lévy adaptedness; source-specific SpectrallyNegativeLevy definition import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_general_strict_prefix_reversal_of_law

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ)
    (ν : Measure Ω) (a : ℝ)
    (hR : ∀ A : Set (Fin n → ℝ), MeasurableSet A →
      ν {ω : Ω | (fun i : Fin n =>
        X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A} =
      ν {ω : Ω | (fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ A}) :
    ν {ω : Ω | ∃ k : Fin n.succ,
      X.X ((n : ℝ≥0) * δ) ω - X.X ((k.val : ℝ≥0) * δ) ω < a} =
    ν {ω : Ω | ∃ k : Fin n.succ,
      X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω < a} := by sorry
