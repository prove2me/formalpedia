-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_finite_activity_standing_source_exists
-- name    : AvramDividend.Classical.avram_a06_bv_finite_activity_standing_source_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:54:58.039224+00:00
-- url     : https://prove2.me/theorems/3281148e-e1e8-4781-9254-1ccba1182757
-- title:
--   A06 concrete positive-drift finite-activity BV Lévy source with diffuse negative jumps
-- statement:
--   Construct on two independent real sequence coordinates a compound-Poisson spectrally negative Lévy process with positive deterministic drift and an absolutely continuous bounded negative jump density, and equip it with its natural filtration. It has finite jump activity and bounded variation; the positive drift with nonzero jump intensity excludes monotone paths; finite-activity gives integrability and density gives Condition33. This is the only source-existence prerequisite for the A06 zero-cap disproof.
-- source:
--   Necessary and independent concrete model existence lemma for disproving the original A06 bounded-variation stochastic core at zero cap. Existing Proved theorem avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample supplies the positive-payoff violating horizon for any source satisfying these hypotheses. Existing Proved barrierStrategy_no_right_jump_of_initial_below_barrier establishes the target's jump condition with w=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_finite_activity_standing_source_exists :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.Standing ∧ X.BoundedVariation ∧
        X.ν (Iio (0 : ℝ)) < ⊤ := by sorry
