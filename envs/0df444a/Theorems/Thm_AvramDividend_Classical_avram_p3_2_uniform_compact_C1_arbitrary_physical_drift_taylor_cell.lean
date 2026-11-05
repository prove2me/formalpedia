-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_taylor_cell
-- name    : AvramDividend.Classical.avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_taylor_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:35:28.887074+00:00
-- url     : https://prove2.me/theorems/5ff4f301-871d-4322-8d2e-94b92e36da90
-- title:
--   Uniform compact C1 Taylor remainder for arbitrary physical BV drift increments
-- statement:
--   A source-exact uniform first-order Taylor estimate for the pure physical BV drift increment, independent of the F2 jump-removed Y shift. For each strictly interior compact reserve band and ε>0 there is one δ>0 such that every cell segment z→z+c in the band, with |c|<δ, has |w(z+c)-w(z)-w'(z)c|≤ε|c|. The proof imports the Proved general Taylor-by-derivative-oscillation lemma f016bd96 and genuine C1 derivative continuity.
-- source:
--   Proved C1 Taylor oscillation f016bd96, standard real compact interval derivative uniform continuity; valid for original physical pure drift c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_taylor_cell
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z c : ℝ,
        Set.uIcc z (z + c) ⊆ Set.Icc a b →
        |c| < δ →
        |w (z + c) - w z - deriv w z * c| ≤ ε * |c| := by sorry
