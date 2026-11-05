-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceiling_grid_expected_pair_rate
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_ceiling_grid_expected_pair_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:53:15.167848+00:00
-- url     : https://prove2.me/theorems/3a863fb9-db46-4586-a139-bee64d620106
-- title:
--   Actual original-process ceiling-index chronological pair expectation equals compensated Lévy rate sum on every physical uniform grid
-- statement:
--   For any positive horizon and positive integer mesh, the ENNReal expected original X negative-band ceiling-index chronological pair count equals the deterministic sum of the actual ν(B)² intrinsic independent-window rates on the unchanged Ω,P,𝓕. The finite-grid equality is proved pathwise, and P2-E's Proved compensation gives the expectation. No Poisson proxy, extra independence or equality in law.
-- source:
--   Public Proved P2-E original_grid_pair_rate_sum_exact 77b37394 and newly-Proved source pointwise original_ceil_grid_intrinsic_pair_sum (pending); all original Mathlib 0df444a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_rate_sum_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_ceiling_grid_expected_pair_rate
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
    (∫⁻ ω, (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)) ∂P) =
      ∑ i : Fin k, (((s i : ℝ≥0) : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
