-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_inner_band_uniform_C1_J_commutator
-- name    : AvramDividend.Classical.avram_p3_f2_original_inner_band_uniform_C1_J_commutator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:29:28.998666+00:00
-- url     : https://prove2.me/theorems/34cffaf7-692e-404e-b198-c1318a257843
-- title:
--   Original source negative-J inner compact band alone controls shifted C1 mixed commutator on fine grids
-- statement:
--   For original X, D, the true negative-jump accumulation J and jump-removed Y, a single inner compact reserve band containing the unshifted raw-J segment suffices to control the shifted Y/J C1 commutator. A positive threshold is the minimum of the uniform derivative modulus and two strict inner-to-outer reserve margins. This removes a difficult independent shifted-segment verification hypothesis from stopped-path P3-G2 integration.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_uniform_compact_C1_negative_J_shift_commutator
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_strict_compact_margin_absorbs_Y_shift_of_J_cell
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_inner_band_uniform_C1_J_commutator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b a₀ b₀ : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ha : a < a₀) (hb : b₀ < b) :
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
          Set.uIcc (z i - j i) (z i) ⊆ Set.Icc a₀ b₀) →
        (∀ i, i < n → |c i| < δ) →
        ∀ i, i < n →
          |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| ≤ ε * |j i| := by sorry
