-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b247_original_true_ruinclipped_uniform_grid_signed_HJB_rightcash_20261114
-- name    : AvramDividend.Classical.avram_b247_original_true_ruinclipped_uniform_grid_signed_HJB_rightcash_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:34:30.079356+00:00
-- url     : https://prove2.me/theorems/27fe94dc-f511-4a1d-84d6-a1c6217815da
-- title:
--   Exact original ruin-clipped physical uniform grid signed HJB generator and right-dividend-cash remainder nonpositive
-- statement:
--   Specialise the Proved finite original stopped-grid signed HJB and right-payment ledger inequality to the actual canonical grid clipped by the original stopping time σ and ruin, including the exact inclusive initial right-payment correction and signed discounted continuous generator drift. For each physical sample path, all cells selected as interior have nonpositive discounted generator drift while every right dividend occurring at time zero or strictly before ruin has nonpositive correction. All time grid points are ordered by the true min truncation. No post-ruin process is involved.
-- source:
--   Proved avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign, with the canonical true clipped physical grid and monotonicity of min(iΔ, σ).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b247_original_true_ruinclipped_uniform_grid_signed_HJB_rightcash_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ω : Ω) (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (y : ℕ → ℝ) (active : ℕ → Bool) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    (∀ i ∈ Finset.range (m + 1), active i = true →
      0 < y i ∧ ENNReal.ofReal (y i) < C) →
    (∑ i ∈ Finset.range (m + 1), if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i + 1) : ℝ) - (v i : ℝ)) *
        (X.generator w (y i) - q * w (y i))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0 := by sorry
