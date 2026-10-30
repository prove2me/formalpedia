-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_surviving_horizon_killed_reward_tendsto
-- name    : AvramDividend.Classical.avram_root29_01_ubv_surviving_horizon_killed_reward_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:34:16.691109+00:00
-- url     : https://prove2.me/theorems/5f86c7a8-b260-487a-b702-bf2e39919e80
-- title:
--   True UBV surviving-horizon continuously killed ceiling-grid reward converges
-- statement:
--   For an actual unbounded-variation Lévy path with true strict lower exit after cap T, the full continuously killed history indicator at every stopped ceiling-mesh clock equals one. The accepted original-P unbounded all-path ceiling-grid raw scale convergence gives the terminal clipped scale reward, even with no upper exit and no Standing assumption.
-- source:
--   WS1A work/avram_root29_01_ubv_surviving_horizon_killed_reward_tendsto_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_strict_preclock_closed_survival

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_surviving_horizon_killed_reward_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (nhds 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (hBefore : (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min
            ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
      atTop
      (nhds (if min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by sorry
