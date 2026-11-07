-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_cutoff_laplace_pathwise_split
-- name    : AvramDividend.Classical.avram_bv_jump8_source_cutoff_laplace_pathwise_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:30:27.522859+00:00
-- url     : https://prove2.me/theorems/a173dbfa-6809-485f-9359-69c0f9321945
-- title:
--   Original marked cutoff Laplace weight splits over adjacent windows almost surely
-- statement:
--   For the genuine intrinsic original marked-jump measure, the (0,n+1] cutoff negative-jump Laplace weight equals the product of (0,n] and (n,n+1] weights, almost surely. The already-Proved full BV jump magnitude bound ensures both half-open lintegrals are finite, avoiding toReal-top artefacts.
-- source:
--   Source exact mission original intrinsic marked random measure. Disjoint window identity and stochastic conditions separated. Closures are combined by Lean integral_congr_ae and two expectation identities. The BV magnitude bound is already Proved 8fdf098e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_source_cutoff_laplace_pathwise_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (n k : ℕ),
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) * Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) := by sorry
