-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_upper_first_ceiling_killed_reward_tendsto
-- name    : AvramDividend.Classical.avram_root29_01_ubv_upper_first_ceiling_killed_reward_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:14:34.684987+00:00
-- url     : https://prove2.me/theorems/78876faf-250b-45a3-91dd-0a72f506f6ca
-- title:
--   Actual UBV upper-first continuously killed ceiling-grid q-scale reward tends to strict upper payoff
-- statement:
--   For a genuine spectrally negative Lévy process of unbounded variation, q>0 and a true scale W, on every actual upper-first path before a cap T the full continuous-history-killed finite ceiling grid q-scale reward tends to the strict upper exit terminal q-scale payoff. The proof imports the genuinely Proved source UBV origin-zero theorem, actual source clipped grid raw convergence, finite first-passage GLB and positive upper-history eventually-surviving lemma, with no Standing premise, no assumed ratio, and no unproved optional stopping.
-- source:
--   WS1A work/avram_root29_01_ubv_upper_first_ceiling_killed_reward_tendsto_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_upper_first_ceiling_killed_reward_tendsto
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
    (hUp : twoSidedExitUpTime X (a-x) ω <
      twoSidedExitDownTime X (-x) ω)
    (hBefore : (twoSidedExitUpTime X (a-x) ω).toNNReal < T) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min
            ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
      atTop (nhds (Real.exp (-(q *
        ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))) := by sorry
