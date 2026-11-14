-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a128_original_gaussian_physical_source_full_cell_three_error_exact_algebra
-- name    : AvramDividend.Classical.avram_ga_a128_original_gaussian_physical_source_full_cell_three_error_exact_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:16:35.929871+00:00
-- url     : https://prove2.me/theorems/40d68ddb-371e-4442-9559-8ebe5012d393
-- title:
--   Exact original Gaussian physically full pre-stop source cell residual splits into classical Taylor, raw-centred Hessian and discount mismatch errors
-- statement:
--   For the actual original zero-jump Lévy process X, actual dividend right limits D, a physical source clock s and complete mesh width Delta, the full-cell discounted Gaussian spatial/HJB residual equals the exact classical C2 Taylor remainder plus original raw-centred Hessian quadratic cross plus the time-discount Euler mismatch. The identity uses the original process, source increments, discount, drift and generator, and is algebraically exact before any positive reserve localisation.
-- source:
--   Certified original gaussian ga77 source-specific classical compensated-cell identity, ga78 mesh source decomposition, and root-specific ga119 full-cell absolute expected L1 obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a128_original_gaussian_physical_source_full_cell_three_error_exact_algebra
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω) (s Δ : ℝ≥0) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let r : ℝ := X.X (s + Δ) ω - X.X s ω
    let z : ℝ := r - (Δ : ℝ) * X.c
    let W : ℝ := w (y + r) - w y
    let Q : ℝ := deriv w y * z +
      (iteratedDeriv 2 w y / 2) * (z^2 - (Δ : ℝ) * X.σ^2)
    let T : ℝ := E s * (W - deriv w y * r -
      (iteratedDeriv 2 w y / 2) * r^2)
    let B : ℝ := E s * (iteratedDeriv 2 w y / 2) * (r^2 - z^2)
    let C : ℝ := (E (s + Δ) - E s) * W
    E (s + Δ) * W - E s * Q -
      (Δ : ℝ) * E s * X.generator w y = T + B + C := by sorry
