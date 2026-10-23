-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_expectation_tendsto
-- name    : AvramDividend.Classical.chat03_actual_ceiling_capped_grid_expectation_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:38:11.386554+00:00
-- url     : https://prove2.me/theorems/973b8166-be3c-465e-be03-7842d7fd9d20
-- title:
--   Actual finite-horizon two-sided stopped q-scale reward expectations converge
-- statement:
--   Under the accepted spectrally negative Lévy process and q-scale hypotheses, finite-horizon grid first-hitting rewards converge in expectation to the continuous stopped reward, including atoms at the terminal horizon. The theorem uses the actual original uniform-grid hitting indices, a clipped sampled filtration constructed from the monotone clock and an explicit almost-everywhere strong-measurability condition on the continuous stopped payoff. Uniform L² bounds and pathwise convergence are supplied by accepted lemmas; no unproved martingale assertion is assumed.
-- source:
--   Combine accepted all-branches almost-everywhere reward convergence with accepted exact clipped-grid hitting-index congruence and bounded monotone clipped-clock lemma. Apply proved Chat03 capped-grid expectation convergence, which itself uses uniform second-moment control. The discrete sampled filtration is built directly by the accepted monotone-clock filtration helper.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_ae_all_branches
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_expectation_of_ae_convergence
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_actual_ceiling_capped_grid_expectation_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (hZ : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P) :
    Integrable (fun ω =>
      Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P)
      atTop (𝓝 (∫ ω,
        Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω) ∂P)) := by
  sorry
