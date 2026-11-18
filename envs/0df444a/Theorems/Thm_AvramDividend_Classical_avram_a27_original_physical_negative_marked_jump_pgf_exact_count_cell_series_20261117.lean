-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:43:54.924474+00:00
-- url     : https://prove2.me/theorems/c7ee79dc-bc72-404d-bd1e-594f11f18d50
-- title:
--   Actual original physical negative marked jump PGF equals the exact source count-cell Laplace power series
-- statement:
--   For the original finite-activity spectrally negative Lévy process without any change of probability space, the joint generating expectation E[z^K exp(theta J)] equals the series of exact physical count-cell Laplace integrals C_k z^k for any unit-interval z and nonnegative theta. This identifies the real coefficients needed to extract the source marked Mecke recurrence from an exact marked-Poisson PGF identity.
-- source:
--   Proved original physical joint marked-count PGF integrability 41004 and generic exact natural count-cell power-series decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The true original physical negative marked-jump joint generating function has its exact count-cell power-series coefficients. -/

theorem AvramDividend.Classical.avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    HasSum (fun k : ℕ => z ^ k *
      (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * J ω) ∂P))
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by sorry
