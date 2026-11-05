-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_compact_C1_jump_cell_four_pairs
-- name    : AvramDividend.Classical.avram_p3_f2_original_stopped_compact_C1_jump_cell_four_pairs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:37:19.555796+00:00
-- url     : https://prove2.me/theorems/8337de42-75f3-4a27-b2fa-a89d06df6d9e
-- title:
--   Original stopped compact interior C1 generates all four physical jump-cell bounds
-- statement:
--   Use the proved original positive-cap openness, compact interior C1-to-Lipschitz estimate and accepted literal original stopped four-point source theorem to obtain one nonnegative local jump constant for the actual finite physical mesh. This directly supplies both tagged and untagged negative-jump pair inequalities of the original strict-cash C1 grid, with only genuine compact-band four-endpoint containment remaining. No compensated jump expectation or artificial source processes.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_open_interior_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_jump_cell_four_pairs_of_local_Lipschitz
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_stopped_compact_C1_jump_cell_four_pairs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a / 2 ≤ b)
    (hBand : Set.Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    (∀ i, i < n → z i ∈ Set.Icc (a / 2) b ∧
      z i + c i ∈ Set.Icc (a / 2) b ∧
      z i - j i ∈ Set.Icc (a / 2) b ∧
      z i + c i - j i ∈ Set.Icc (a / 2) b) →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i, i < n →
      (|w (z i + c i - j i) - w (z i - j i)| ≤ L * |c i|) ∧
      (|w (z i + c i) - w (z i)| ≤ L * |c i|) ∧
      (|w (z i + c i - j i) - w (z i + c i)| ≤ L * |j i|) ∧
      (|w (z i - j i) - w (z i)| ≤ L * |j i|) := by sorry
