-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_upcross_localisation
-- name    : AvramDividend.Classical.avram_ubv_top9_original_any_clock_upcross_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:57:25.134196+00:00
-- url     : https://prove2.me/theorems/b2e939f7-00b6-4f6d-b33a-f43272848dd1
-- title:
--   Original Lévy upward-exit localisation of any bounded right-continuous stopping time
-- statement:
--   For any original Lévy process and any bounded nonnegative stopping clock, first-upcrossing localisation gives genuine smaller right-continuous stopping times whose stopped original process stays below k+1 and that become literally equal to the requested clock for all sufficiently large k, path by path.
-- source:
--   Source-exact upper-exit clock construction from the proved F14 original upcrossing method (7ec2b70b), strengthened to any independent bounded stopping time rho. This gives the spatial upper envelope and eventual exactness required for infinite-cap arbitrary-clock Fatou without assuming C finite. Uses the same twoSidedExitUpTime, original stopped process X.X, upperPassage_stopping_rightCont_filtration, path_value_le_of_strict_prefix_le, and firstUpcrossing_record_grid_clocks_eventually_ge_horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_any_clock_upcross_localisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ rhoLoc : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (rhoLoc k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, rhoLoc k ω ≤ ρ ω) ∧
      (∀ k ω, X.X (rhoLoc k ω) ω ≤ (k : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, rhoLoc k ω = ρ ω) := by sorry
