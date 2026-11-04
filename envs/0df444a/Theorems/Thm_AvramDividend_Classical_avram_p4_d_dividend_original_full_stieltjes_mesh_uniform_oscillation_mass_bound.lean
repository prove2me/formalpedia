-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_mesh_uniform_oscillation_mass_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_mesh_uniform_oscillation_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:46:52.660311+00:00
-- url     : https://prove2.me/theorems/a337c760-2387-4685-94c6-8f428d0e913b
-- title:
--   Original Stieltjes mesh error bounded by uniform oscillation times complete cell mass
-- statement:
--   For finite original dividend-payment cells, if every nonnegative ENNReal discount oscillation bound delta_i is at most the common epsilon, the sum of delta_i times original full cell Stieltjes mass is at most epsilon times the complete sum of cell masses. This retains singular-continuous and atomic dividend payments and is the final order estimate needed to reduce finite mesh error to a total mass bound.
-- source:
--   Original dividendMeasure as a nonnegative Stieltjes measure; finite sum monotonicity and distributivity in Mathlib

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_mesh_uniform_oscillation_mass_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : Finset ι) (a b : ι → ℝ≥0)
    (δ : ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hδ : ∀ i ∈ s, δ i ≤ ε) :
    (∑ i ∈ s, δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) ≤
      ε * (∑ i ∈ s, dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by sorry
