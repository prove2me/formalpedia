-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_uniform_interior_C1_mesh_oscillation
-- name    : AvramDividend.Classical.avram_p3_f2_original_stopped_uniform_interior_C1_mesh_oscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:28:55.954832+00:00
-- url     : https://prove2.me/theorems/c71d50e6-5c39-464f-a154-12b40066cfe9
-- title:
--   Uniform derivative oscillation and integrability for original BV stopped interior source meshes
-- statement:
--   For the actual original Lévy negative-jump-removed source increments and right-limit controlled reserve, C1 regularity on the positive subcap domain gives one uniform derivative modulus on an arbitrary fixed compact interior reserve band. Every original source cell contained in that band and with sufficiently short actual continuous-source increment has both genuine interval integrability of deriv w and the exact per-cell derivative oscillation required by the stopped C1 Taylor bridge. Ruin and cap-contact cell containment still require genuine stopping/localisation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_stopped_uniform_interior_C1_mesh_oscillation
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
      (∀ i, i < n →
        Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
      (∀ i, i < n → |c i| < δ) →
      (∀ i, i < n →
        IntervalIntegrable (deriv w) volume (z i) (z i + c i) ∧
        ∀ v ∈ Set.uIoc (z i) (z i + c i),
          |deriv w v - deriv w (z i)| ≤ ε) := by sorry
