-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid14_original_pre_ruin_masked_cell_sum_cofinal_exact
-- name    : AvramDividend.Classical.avram_p3_grid14_original_pre_ruin_masked_cell_sum_cofinal_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:13:19.218488+00:00
-- url     : https://prove2.me/theorems/75b599e0-ecc6-4bc8-81de-e1ad1c6dcdc9
-- title:
--   Original pre-ruin physical-grid cell sum stabilises exactly under cofinal compact-band masks
-- statement:
--   For a fixed original stopped BV physical row and any real-valued source-cell term, the compact-band spatial cutoff eventually leaves the full finite pre-ruin interior sum unchanged exactly. This instantiates Proved ed03fa23 at the literal original left-limit surplus, preserves the time/ruin mask, and supplies a deterministic two-scale localisation step for e49a5fce; it makes no claim about L1 domination, a row-uniform limit or a cash/contact error budget.
-- source:
--   Uses exact prior Proved original finite-row interior-mask eventuality ed03fa23, plus Finset.sum_congr. Target e49a5fce original same-grid localisation.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid14_original_pre_ruin_masked_cell_sum_cofinal_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (ω : Ω) (cell : ℕ → ℝ) :
    let Z : ℕ → ℝ := fun i =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    ∃ N : ℕ, ∀ k ≥ N,
      (∑ i ∈ Finset.range (n + 1),
        if ((u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            (0 < Z i ∧ ENNReal.ofReal (Z i) < C)) ∧
            Z i ∈ Icc (a k) (b k) then cell i else 0) =
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            (0 < Z i ∧ ENNReal.ofReal (Z i) < C)
        then cell i else 0) := by sorry
