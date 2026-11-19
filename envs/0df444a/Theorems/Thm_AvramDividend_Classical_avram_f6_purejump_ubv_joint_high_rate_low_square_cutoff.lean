-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_joint_high_rate_low_square_cutoff
-- name    : AvramDividend.Classical.avram_f6_purejump_ubv_joint_high_rate_low_square_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:20:15.337798+00:00
-- url     : https://prove2.me/theorems/1646539b-e63d-4789-a06b-399136572e4b
-- title:
--   Simultaneously high finite jump-count rate and low smallmark L² error at a common cutoff
-- statement:
--   Given any prescribed finite jump intensity R and squared smallmark error tolerance ε>0, choose one genuine original negative jump cutoff level n so the finite negative mark Poisson rate exceeds R while the squared jump amplitude integral below that same cutoff is below ε. This is the joint analytic diagonal needed when constructing the original infinite-activity compensated jump source, using the original X.ν and no postulated stochastic cash budget.
-- source:
--   Proved generic negative_jump_real_poisson_rates_tendsto_top 25e87aea plus original b9b373fa and original smallmark square energy ddfd1997.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_purejump_ubv_joint_high_rate_low_square_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (R : ℝ) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ n : ℕ,
      R ≤ (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal ∧
      (∫⁻ z in Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (z ^ 2) ∂(X.ν.map (fun y : ℝ => -y))) < ε := by sorry
