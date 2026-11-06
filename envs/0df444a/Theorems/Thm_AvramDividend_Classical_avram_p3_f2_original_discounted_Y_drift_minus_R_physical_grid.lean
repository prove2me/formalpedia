-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_Y_drift_minus_R_physical_grid
-- name    : AvramDividend.Classical.avram_p3_f2_original_discounted_Y_drift_minus_R_physical_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:26:33.017339+00:00
-- url     : https://prove2.me/theorems/7ee56b50-186f-49be-8b51-8bac13077f1a
-- title:
--   Original stopped BV physical discounted Y derivative grid decomposes into Lévy drift minus R increments
-- statement:
--   On the actual original spectrally negative Lévy process, with its raw negative-jump accumulator J, the jump-removed path Y equals deterministic t·X.drift minus the genuine R residual path. The exact weighted finite physical grid sum of derivatives at original postdividend reserves thus splits into deterministic drift-weighted elapsed time and an explicit R increment sum. This algebraic bridge is the missing source Y-term interface for stopped C1 verification, without assuming stochastic mean-zero or expectation convergence.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_discounted_Y_drift_minus_R_physical_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      e i * (deriv w (z i) * (Y (u (i + 1)) - Y (u i)))) =
      (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) * (R (u (i + 1)) - R (u i)))) := by sorry
