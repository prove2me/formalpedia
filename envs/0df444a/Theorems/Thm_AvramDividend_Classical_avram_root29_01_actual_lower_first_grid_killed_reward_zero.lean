-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_lower_first_grid_killed_reward_zero
-- name    : AvramDividend.Classical.avram_root29_01_actual_lower_first_grid_killed_reward_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:59:17.76935+00:00
-- url     : https://prove2.me/theorems/19c5c4a0-e170-4a4c-9ef3-a231b35f67fd
-- title:
--   True original-Lévy lower-first sampled continuously killed q-scale payoff tends to zero
-- statement:
--   On a true original-P two-sided first-exit path τ<T whose terminal q-scale vanishes, the exact Mathlib hittingBtwn grid sampled discounted payoff converges to zero by a Proved source clock limit. Its continuously lower-history-killed counterpart therefore also converges to zero by the accepted nonnegative squeeze lemma. There is no assumption of eventual detection of a negative excursion and no circular two-sided exit identity.
-- source:
--   WS1A work/avram_root29_01_actual_lower_first_grid_killed_reward_zero_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_lower_first_grid_killed_reward_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) (hWnonneg : ∀ z, 0 ≤ W z)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτT : τ < T) (hEndZero : W (x + X.X τ ω) = 0)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ (K n η : ℝ≥0) * mesh n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (((K n η : ℝ≥0) * mesh n) : ℝ))) *
          W (x + X.X ((K n η : ℝ≥0) * mesh n) η)) ω)
      atTop (nhds 0) := by sorry
