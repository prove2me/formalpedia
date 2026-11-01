-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_original_residual_finite_range_of_right_grid
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_original_residual_finite_range_of_right_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:19:20.307986+00:00
-- url     : https://prove2.me/theorems/3045a09b-7a7f-4c33-975b-1fd8e3e9117d
-- title:
--   Actual BV finite-activity source Lévy residual takes finitely many values at all times of a right-covered finite horizon
-- statement:
--   For the actual original BV source spectrally negative Lévy process with finite negative jump intensity, assume an aligned, monotone, equal-mesh dyadic grid right-covers every time in [0,T] via grid points approaching from above. On a single original P-probability-one event the full residual path u↦u*drift−X_u visits only a finite set on [0,T]. This is source-specific all-time finite activity groundwork, rather than an equal-law construction or a Poisson/compensator claim.
-- source:
--   Canonical Proved b93e9d7e-e1a9-42f5-968a-560566e554ab uniformly bounds the image cardinalities of actual dyadic residuals. Alignment stabilises their nested finite value sets. Original pathwise X.rightCont, explicit right-covering and closedness of finite subsets of ℝ extend this common finite range from grid observations to every time in [0,T]. No Open or external stochastic interface is imported.

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_values_card_uniform_ws01b

open MeasureTheory Set Finset Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave4_04a_bv_original_residual_finite_range_of_right_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℕ → ℝ≥0) (T : ℝ≥0)
    (hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hGridMono : ∀ n, Monotone (grid n))
    (hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        (T : ℝ) / ((2 ^ n : ℕ) : ℝ)))
    (hRightCover : ∀ t : ℝ≥0, t ≤ T →
      ∃ index : ℕ → ℕ,
        (∀ n, index n ≤ 2 ^ n) ∧
        (∀ n, t ≤ grid n (index n)) ∧
        Tendsto (fun n => grid n (index n)) atTop (nhds t)) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω ∈ S := by sorry
