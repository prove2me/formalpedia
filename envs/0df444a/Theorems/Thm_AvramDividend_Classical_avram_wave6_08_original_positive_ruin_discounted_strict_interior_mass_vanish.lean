-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_discounted_strict_interior_mass_vanish
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_strict_interior_mass_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:15:33.576238+00:00
-- url     : https://prove2.me/theorems/54a673aa-95e0-4610-97c0-d6447beb7761
-- title:
--   Original discounted strictly pre-ruin full Stieltjes terminal-cell reward vanishes
-- statement:
--   For every nonnegative discount rate, the genuine original fully weighted dividend Stieltjes cash-flow inside the strictly pre-ruin shrinking final open cell tends to zero. This controls all singular-continuous and interior atomic payments while excluding a potential right dividend at the ruin instant, using exact source terminal measure convergence and the bound exp(-qt)≤1 for t≥0.
-- source:
--   Actual strict-left full Stieltjes terminal cell mass and direct discount bounded by one, plus general squeeze for ENNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_interior_mass_vanish

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_strict_interior_mass_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => ∫⁻ t in Ioo (u n : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by sorry
