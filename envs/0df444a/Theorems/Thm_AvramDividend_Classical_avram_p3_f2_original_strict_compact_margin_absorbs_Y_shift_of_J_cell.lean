-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_strict_compact_margin_absorbs_Y_shift_of_J_cell
-- name    : AvramDividend.Classical.avram_p3_f2_original_strict_compact_margin_absorbs_Y_shift_of_J_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:23:53.461041+00:00
-- url     : https://prove2.me/theorems/94f41c7f-273c-42c2-a954-321710d4489e
-- title:
--   Actual original J physical-cell strict compact interior margin absorbs small jump-removed Y shift
-- statement:
--   For the actual negative-jump raw cumulative J, jump-removed path Y, original reserve X-rightLimit(D), and a finite physical clock grid, a strict inner compact reserve segment automatically certifies the shifted segment in a slightly larger outer compact band whenever the original Y increment is smaller than the two actual interior margins. This closes the shifted-base geometric premise of the mixed source C1 theorem without assuming a second separately certified stopped segment.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_strict_compact_margin_absorbs_Y_shift_of_J_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (a b a₀ b₀ : ℝ) (ha : a < a₀) (hb : b₀ < b) :
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
      (∀ i, i < n → |c i| < min (a₀ - a) (b - b₀)) →
      ∀ i, i < n →
        Set.uIcc (z i + c i - j i) (z i + c i) ⊆
          Set.Icc a b := by sorry
