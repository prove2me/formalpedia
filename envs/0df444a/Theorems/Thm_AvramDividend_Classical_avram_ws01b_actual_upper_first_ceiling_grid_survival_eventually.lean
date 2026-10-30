-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
-- name    : AvramDividend.Classical.avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:53:05.31456+00:00
-- url     : https://prove2.me/theorems/4b15e831-4381-4725-ad11-ec30904c1132
-- title:
--   Actual upper-first finite-exit stopped sampling clocks eventually preserve killed survival
-- statement:
--   On every original Lévy path with first strict two-sided exit at the strict upper barrier before the time cap, the true first ceiling-grid exit clock converges to that upper time and hence is eventually strictly earlier than the lower ruin clock. Therefore all sampled stopped histories have nonnegative reserve, ensuring the actual killed indicator is identically one eventually. The result uses no substitute process or BV limit W(0)=0.
-- source:
--   Canonical pathwise source finite first-exit GLB, positive-margin actual first-hitting grid lemma, capped-grid clock convergence, and the proved lower-clock closed-history stability under time convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_eventually_closed_survival_of_mesh_tendsto

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (a x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < -x ∨ a-x < X.X t ω} τ)
    (hτUp : (τ : ℝ≥0∞) = twoSidedExitUpTime X (a-x) ω)
    (hup : twoSidedExitUpTime X (a-x) ω <
      twoSidedExitDownTime X (-x) ω)
    (hbefore : τ < T)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    ∀ᶠ n in atTop,
      ∀ s : ℝ≥0, s ≤ min ((K n ω : ℝ≥0) * mesh n) T →
        0 ≤ x + X.X s ω := by sorry
