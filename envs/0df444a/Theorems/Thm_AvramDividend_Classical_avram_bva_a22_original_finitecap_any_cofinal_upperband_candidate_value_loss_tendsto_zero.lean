-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_finitecap_any_cofinal_upperband_candidate_value_loss_tendsto_zero
-- name    : AvramDividend.Classical.avram_bva_a22_original_finitecap_any_cofinal_upperband_candidate_value_loss_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:13:40.806218+00:00
-- url     : https://prove2.me/theorems/f37ba5c8-a353-43b9-854a-c9c9c4cd3232
-- title:
--   Original finite-cap arbitrary cofinal upper spatial candidate value gap vanishes at the actual cap with no band-rate hypothesis
-- statement:
--   Under the original dividend model with a finite strictly positive reserve cap C represented by a positive real L, let w be the original continuously defined candidate on the nonnegative reserve side and let a_n,b_n be arbitrary prescribed original positive cofinal spatial bands strictly contained below C. Prove that the genuine cap-side candidate increment w(L)-w(b_n) tends to zero. The Proved exact finite-cap cofinal upper endpoint theorem gives b_n to L with no monotonicity, nesting or rate relative to the original physical clock mesh, and original positive band conditions ensure b_n remains nonnegative. By original restricted continuity at the cap, w(b_n) tends to w(L). This is the deterministic candidate cap-side localisation loss term needed to remove finite-cap spatial truncations in the original BV stopped C1 ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_finitecap_any_cofinal_upperband_candidate_value_loss_tendsto_zero
    (C : ℝ≥0∞) (L : ℝ) (hL : 0 < L)
    (hCL : C = ENNReal.ofReal L)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto (fun n => w L - w (b n)) atTop (𝓝 (0 : ℝ)) := by sorry
