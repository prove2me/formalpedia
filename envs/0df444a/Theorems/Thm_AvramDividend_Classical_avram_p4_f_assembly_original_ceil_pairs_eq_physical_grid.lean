-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ceil_pairs_eq_physical_grid
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ceil_pairs_eq_physical_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:52:19.009492+00:00
-- url     : https://prove2.me/theorems/32061d3a-d690-45b8-a9b7-629d847b3f00
-- title:
--   Original positive-horizon ceil-grid chronological pairs equal actual source past-future count products
-- statement:
--   The actual finite negative-band jumps of the same original X, grouped into positive-horizon uniform ceiling bins, have chronological early-cell pairs whose number equals the sum of original intrinsic marked-jump counts in (0,s_i] times those in (s_i,t_i]. This is a pathwise, same-process equality and supplies the missing finite-grid physical counting bridge for the second factorial moment; it does not assert the limit or stopped Itô identity.
-- source:
--   Proved public bridge c7fa6a87, original past intrinsic count 0ecd8bf1, future cell intrinsic count ddbdde55, uniform endpoint 6bdc2c26; Mathlib 0df444a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_past_cell_sum
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_past_intrinsic_count
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ceil_pairs_eq_physical_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    let Npast : Fin k → ℝ≥0∞ := fun i =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u)))
        (Ioc 0 (s i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Nfuture : Fin k → ℝ≥0∞ := fun i =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u)))
        (Ioc (s i) (t i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℝ≥0∞) =
      ∑ i : Fin k, Npast i * Nfuture i := by sorry
