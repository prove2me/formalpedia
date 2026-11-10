-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich
-- name    : AvramDividend.Classical.avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:26:26.570087+00:00
-- url     : https://prove2.me/theorems/d924a79e-19f1-4dff-bee1-86dac324b917
-- title:
--   Original annulus factorial moment squeezed between physical chronological cells and full-band collision bound
-- statement:
--   For the original negative-annulus physical count N and every finite number of uniform cells k+1, the expected factorial N(N-1) is integrable and lies between the exact off-diagonal original annulus mean, equal to the annulus squared rate times k/(k+1), and that quantity plus the original full-upper-cutoff squared rate divided by k+1. This follows from source-exact finite time splitting, Proved f56b2229 factorial telescoping, de84ed95 original annulus grid cross means, and 69f9bc6c shifted full-cutoff factorial moments. It is the single analytic grid-estimate premise needed to close 6ea0212e by k tending to infinity, with no independent mark model or auxiliary process.
-- source:
--   Root-connected: original 6ea0212e annulus factorial exact -> 6e234a3f physical annulus L2 isometry -> mixed Gaussian residual. Proved f56b2229, de84ed95, 0060f5ce, 69f9bc6c, 61ef9f16 furnish the required algebra, grid mean, pathwise finiteness, diagonal domination and time partition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let rM : ℝ := ((T : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((m : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      ∀ k : ℕ,
        let q : ℝ := ((k + 1 : ℕ) : ℝ)
        rB ^ 2 * (1 - 1 / q) ≤
          (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) ∧
        (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) ≤
          rB ^ 2 * (1 - 1 / q) + rM ^ 2 / q := by sorry
