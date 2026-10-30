-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_surviving_cap_killed_reward_tendsto
-- name    : AvramDividend.Classical.avram_root29_01_actual_surviving_cap_killed_reward_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:43:43.019726+00:00
-- url     : https://prove2.me/theorems/854c975d-2bf7-4080-8911-c25247466cc2
-- title:
--   Actual no-ruin finite-horizon grid histories preserve the raw q-scale limit
-- statement:
--   For an actual source Lévy path whose reserve never becomes negative on the entire finite horizon [0,T], every sampled stopped horizon bounded by T also retains the complete continuous lower-survival history. Thus its killed discounted q-scale payoff agrees at every mesh with the unrestricted reward, and any established unrestricted stopped payoff limit transfers unchanged. This supplies the no-exit-before-cap branch of genuine stopped-grid optional-stopping convergence without assuming an exit ratio.
-- source:
--   WS1A work/avram_root29_01_actual_surviving_cap_killed_reward_tendsto_draft.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_surviving_cap_killed_reward_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (T : ℝ≥0) (t : ℕ → ℝ≥0)
    (ht : ∀ n, t n ≤ T)
    (hBefore : ∀ s : ℝ≥0, s ≤ T → 0 ≤ x + X.X s ω)
    (q : ℝ) (W : ℝ → ℝ) (y : ℝ)
    (hRaw : Tendsto (fun n =>
      Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω))
      atTop (nhds y)) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) η)) ω) atTop (nhds y) := by sorry
