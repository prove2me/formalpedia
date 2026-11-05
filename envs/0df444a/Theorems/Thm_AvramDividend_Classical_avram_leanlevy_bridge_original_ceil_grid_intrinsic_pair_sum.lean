-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:37:54.820604+00:00
-- url     : https://prove2.me/theorems/3bf8aa71-5dee-40ef-be27-9c9294fdba04
-- title:
--   Original physical ceiling-grid chronological pair count is the intrinsic past-window times cell-count sum
-- statement:
--   For the literal negative-band marked-time Finset of Avram's original X on the original Ω and P, every positive deterministic physical uniform mesh has ceiling-index pair cardinal equal to the same original intrinsic jump count sum over past × next half-open cells. Explicit endpoint hypotheses and marked-time positivity derived from the original marked Finset preserve exact source data and avoid any equality-in-law transfer. This is the pathwise missing adapter to the already-Proved source compensated finite-grid mean.
-- source:
--   Public source original-grid Fin pair card e4059cbe, ceiling-grid sum allmesh/ceil-grid-past-cell-sum, original P2-E window count 0d0d4845, P2-E finite-grid expected rate 77b37394; all dependencies must be Proved before submitting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_past_cell_sum
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_past_intrinsic_count
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k)
    (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i) (htT : ∀ i, t i ≤ T)
    (hs : ∀ i, (s i : ℝ) = (i.val : ℝ) * (T : ℝ) / (k : ℝ))
    (ht : ∀ i, (t i : ℝ) = ((i.val + 1 : ℕ) : ℝ) * (T : ℝ) / (k : ℝ)) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    ∀ ω, (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)) =
      ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω := by sorry
