-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB48_original_short_barrier_clock_cash_strict_excess
-- name    : AvramDividend.Classical.avram_gbB48_original_short_barrier_clock_cash_strict_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:41:39.948198+00:00
-- url     : https://prove2.me/theorems/db82b46e-e42c-421f-bae3-15512a957849
-- title:
--   Original short cap-barrier stopping clock and conditional cash excess
-- statement:
--   On the original cap-reflected Lévy reserve tube, the lower hit clock equals T, and if the exact short-horizon discounted cash identity holds with the terminal reserve below the cap, the fixed-band pathwise bound is strictly violated. The stochastic cash identity is explicitly a hypothesis, not a claimed proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_short_horizon_cash_identity_contradiction
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB48_original_short_barrier_clock_cash_strict_excess
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
  (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ))
  (hYhi : riskProcess X (1 / 8 : ℝ)
    (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤ (1 / 8 : ℝ))
  (F N : ℝ)
  (hCash : F - (1 / 8 : ℝ) - N =
    (193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 100000 : ℝ))) +
    Real.exp (-(1 / 100000 : ℝ)) *
      (riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω -
        4 * (riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω) ^ 2 -
        15 / 242) - (1 / 1936 : ℝ)) :
  sInf ((Icc (0 : ℝ≥0) T ∩
    (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
      Ici (-(5 / 44 : ℝ))) ∪ {T}) = T ∧
  ¬ F - (1 / 8 : ℝ) ≤ N + (1 / 1936 : ℝ) := by sorry
