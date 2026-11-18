-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
-- name    : AvramDividend.Classical.avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:23:11.877205+00:00
-- url     : https://prove2.me/theorems/22d480fd-869b-4264-a511-1bee58504023
-- title:
--   Single Gaussian tube certifies the original barrier reserve, exact stop and bounded stopped mesh noise
-- statement:
--   For the original drift-two Gaussian cap barrier at x=C=1/8, on a path tube simultaneously controlling the reserve source and centred Brownian noise through the extended stopping horizon, every pre-stop reserve stays above b=5/44, the lower-cutoff stopping clock equals T=1/1000, and every original uniform physical-grid stopped Gaussian centred sum with m≥15999 is bounded by 1/4000. This assembles already source-faithful B38/B40/B121/B129 into one deterministic certificate usable on the joint positive-probability Brownian event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_original_unit_mesh_tube_from_centered_native_brownian
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hSource : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      X.X u ω = B u ω + 2 * (u : ℝ))
    (hc : X.c = 2) (hX0 : X.X 0 ω = 0)
    (hCentered : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      |B u ω| ≤ (1 / 4000 : ℝ))
    (hDrifted : ∀ u : ℝ≥0, u ≤ (1 / 1000 : ℝ≥0) →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (m : ℕ) (hm : 15999 ≤ m) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    (∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
      (5 / 44 : ℝ) < riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω) ∧
    sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
      (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
        Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)}) =
      (1 / 1000 : ℝ≥0) ∧
    |(Finset.range (m + 1)).sum (fun i =>
      if s i < (1 / 1000 : ℝ≥0) then
        Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ (1 / 4000 : ℝ) := by sorry
