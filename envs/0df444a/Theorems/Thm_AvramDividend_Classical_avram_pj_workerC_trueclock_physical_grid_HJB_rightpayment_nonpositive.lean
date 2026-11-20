-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_trueclock_physical_grid_HJB_rightpayment_nonpositive
-- name    : AvramDividend.Classical.avram_pj_workerC_trueclock_physical_grid_HJB_rightpayment_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:41:33.545014+00:00
-- url     : https://prove2.me/theorems/7fa7ced0-bc9c-4264-8d08-bbe99c9579ef
-- title:
--   Genuine original ruin-clipped subordinate physical grid HJB plus all pre-ruin right-dividend jump corrections are pathwise nonpositive
-- statement:
--   For a real original subordinate clock rho dominated by the exact min(true ruin time,n) and the canonical physical grid v_i=min(i*n/(m+1),rho(ω)), all interior active grid-cell HJB discounted drifts and all finite pre-ruin right dividend payment jump corrections together have nonpositive sum. The actual riskProcess is used in every HJB evaluation, actual postpayment rightLimit D at every dividend atom, and no artificial clock or generator inputs. Combines Proved subordinate-clock bound with Proved full original b247 uniform-grid HJB plus right-cash sign.
-- source:
--   Proved aa16b9d8/edebe535 original rho bounded horizon/ruin and Proved 27fe94dc original uniform true-ruinclipped HJB/right-payment sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_b247_original_true_ruinclipped_uniform_grid_signed_HJB_rightcash_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_trueclock_physical_grid_HJB_rightpayment_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (m : ℕ) (ω : Ω) (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (active : ℕ → Bool) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    (∀ i ∈ Finset.range (m + 1), active i = true →
      0 < riskProcess X x D (v i) ω ∧
        ENNReal.ofReal (riskProcess X x D (v i) ω) < C) →
    (∑ i ∈ Finset.range (m + 1), if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i + 1) : ℝ) - (v i : ℝ)) *
        (X.generator w (riskProcess X x D (v i) ω) -
          q * w (riskProcess X x D (v i) ω))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0 := by sorry
