-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_past_intrinsic_count
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_past_intrinsic_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:20:38.11586+00:00
-- url     : https://prove2.me/theorems/0ecd8bf1-6b38-4769-8b31-ca4d0d00360c
-- title:
--   Original Lévy past negative-band intrinsic count equals a ceiling-index sublevel cardinal
-- statement:
--   For the original finite negative-band jump-time set F of the same X, and an actual positive uniform grid, the number of marked source times with ceiling index at most i equals the physical intrinsic count N_X((0,s]×B), with s=iT/k. This source adapter is the past-factor companion to the exact ceiling-cell factor, needed to identify P4-F's physical pair-count grid with the original P2-E cross-window expected product. The natural marked-time positivity property is explicit.
-- source:
--   Pinned Nat.ceil_le and division inequalities, public original intrinsic window cardinal 0d0d4845, physical marked-time finiteness e5e6f70b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_past_intrinsic_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (hk : 0 < k) (i : ℕ)
    (s : ℝ≥0) (hsT : s ≤ T)
    (hs : (s : ℝ) = (i : ℝ) * (T : ℝ) / (k : ℝ))
    (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (hpos : ∀ u ∈ F, (0 : ℝ≥0) < u) :
    (((F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i)).card : ℕ) : ℝ≥0∞) =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) := by sorry
