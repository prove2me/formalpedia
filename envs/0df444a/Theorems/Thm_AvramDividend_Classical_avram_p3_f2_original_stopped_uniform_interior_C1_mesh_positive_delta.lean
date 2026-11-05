-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_uniform_interior_C1_mesh_positive_delta
-- name    : AvramDividend.Classical.avram_p3_f2_original_stopped_uniform_interior_C1_mesh_positive_delta
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:45:54.161364+00:00
-- url     : https://prove2.me/theorems/37a92488-7aa0-4303-9e38-f537a0d3e0c6
-- title:
--   Original stopped C1 source-cell modulus with an explicitly positive uniform mesh threshold
-- statement:
--   Corrects the uniform positive interior mesh threshold quantifier to assert both delta positivity and its implication-bound source-cell C1 oscillation. Uses exact original Lévy negative-jump-removed increments, genuine controlled pre-rightpayment reserve, compact positive-cap C1 regularity and local interval integrability. Unlike the earlier syntactically ambiguous formulation, positivity is a proved output, allowing a refining physical stopped mesh to use the delta directly.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_stopped_uniform_interior_C1_mesh_positive_delta
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ((∀ i, i < n →
        Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
      (∀ i, i < n → |c i| < δ) →
      (∀ i, i < n →
        IntervalIntegrable (deriv w) volume (z i) (z i + c i) ∧
        ∀ v ∈ Set.uIoc (z i) (z i + c i),
          |deriv w v - deriv w (z i)| ≤ ε)) := by sorry
