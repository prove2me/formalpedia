-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_uniform_compact_C1_negative_J_shift_commutator
-- name    : AvramDividend.Classical.avram_p3_f2_original_uniform_compact_C1_negative_J_shift_commutator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:05:49.534057+00:00
-- url     : https://prove2.me/theorems/837da71f-42ea-40b1-93f9-49b8a97b083e
-- title:
--   Uniform original source compact C1 bound on the mixed Y and raw negative-J physical-cell commutator
-- statement:
--   For actual original Lévy X, admissible dividend D and the genuine raw negative-jump series J and jump-removed Y on a finite physical clock grid, uniform continuity of the C1 derivative on one strict compact reserve band controls the mixed shifted Y-J value commutator by epsilon times the original negative-J jump mass, uniformly for all cells whose two shifted J segments remain in the common band and whose Y increment is sufficiently small. This is the missing source-exact condition needed to combine the proved discounted full-cash finite-grid identity with the proved raw-J total variation telescope.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_uniform_compact_C1_negative_J_shift_commutator
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
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
        (∀ i, i < n →
          Set.uIcc (z i - j i) (z i) ⊆ Set.Icc a b) →
        (∀ i, i < n →
          Set.uIcc (z i + c i - j i) (z i + c i) ⊆ Set.Icc a b) →
        (∀ i, i < n → |c i| < δ) →
        ∀ i, i < n →
          |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| ≤ ε * |j i| := by sorry
