-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
-- name    : AvramDividend.Classical.levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:49:52.505249+00:00
-- url     : https://prove2.me/theorems/c35e351b-bb7b-41d4-9138-fb859c5f8868
-- title:
--   Uniform finite-grid one-sided discounted upcrossing bounds pass to the true Lévy first-passage payoff
-- statement:
--   Assume a spectrally negative Lévy process and a sequence of positive uniform mesh sizes shrinking to zero. For any q≥0, threshold z, and ENNReal bound B, assume the q-discounted finite-grid FIRST UPPER passage expectation is at most B for every mesh. Prove the actual (continuous-time) unrestricted first-upcrossing discounted expectation is also ≤B. Use Proved grid-upclock convergence, absence of grid exit when continuous upclock=∞, measurability of uniform grid clocks, the Proved upper-first payoff convergence theorem with the artificial lower clock constantly +∞, and the Proved dominated-convergence theorem for bounded discounted ENNReal payoffs. The only unproved core left for the ultimate Esscher inequality becomes establishing the finite-grid expectation bound B=exp(-φz) at the positive root. This lemma itself should compile with no Open imports.
-- source:
--   Prove2Me proved Chat03 uniform grid measurable clocks, strict first-passage convergence, discounted payoff and lintegral convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (z : ℝ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (B : ℝ≥0∞)
    (hgrid : ∀ n : ℕ,
      (∫⁻ ω : Ω,
        let up := ⨅ k : ℕ,
          if z < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < (⊤ : ℝ≥0∞)
          then ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal up)))
          else 0 ∂P) ≤ B) :
    (∫⁻ ω : Ω,
      if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
      then ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X z ω))))
      else 0 ∂P) ≤ B := by sorry
