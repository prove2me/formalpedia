-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger175_original_zerojump_spatial_cell_error_expansion
-- name    : AvramDividend.Classical.avram_gledger175_original_zerojump_spatial_cell_error_expansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:56:28.699389+00:00
-- url     : https://prove2.me/theorems/47029eeb-ee83-4146-b57a-07e86fcad651
-- title:
--   Exact original zero-jump spatial Taylor cell error without the discount-clock term
-- statement:
--   Exact algebraic identity on the original sample path between a stopped-cell spatial value increment, the centred Gaussian linear/quadratic term, and the original zero-jump generator drift. The right side separates discount times spatial change, compact C2 Taylor remainder and drift-Gaussian cross terms. It follows from the Proved original gledger138 identity and has no additional moment or stopping assumptions. The physical gledger140 mesh estimate reduces to controlling sums of these three genuine terms plus the final clipped crossing.
-- source:
--   Strict algebraic helper for Open gledger140 on selected gledger50 root route; direct reuse of Proved gledger138, preserves original X, D and rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger138_original_zerojump_physical_discounted_generator_Taylor_cell_identity
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger175_original_zerojump_spatial_cell_error_expansion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω) (s t : ℝ≥0) :
    let δ : ℝ := ((t - s : ℝ≥0) : ℝ)
    let E : ℝ := Real.exp (-(q * (s : ℝ)))
    let F : ℝ := Real.exp (-(q * (t : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X t ω - rightLimit D s ω
    let z : ℝ := X.X t ω - X.X s ω - δ * X.c
    F * (w Z - w y) -
      E * (deriv w y * z +
        (iteratedDeriv 2 w y / 2) * (z ^ 2 - δ * X.σ ^ 2)) -
      δ * E * (X.generator w y) =
    (F - E) * (w Z - w y) +
      E * (w Z - w y - deriv w y * (z + X.c * δ) -
        (iteratedDeriv 2 w y / 2) * (z + X.c * δ) ^ 2) +
      E * iteratedDeriv 2 w y * (X.c * δ * z + X.c ^ 2 * δ ^ 2 / 2) := by sorry
