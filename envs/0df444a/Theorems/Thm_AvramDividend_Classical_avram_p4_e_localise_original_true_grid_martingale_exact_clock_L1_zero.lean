-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_grid_martingale_exact_clock_L1_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_grid_martingale_exact_clock_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:53:01.868876+00:00
-- url     : https://prove2.me/theorems/e4d2f1c1-d3e3-430d-a15e-cc1b1f53485e
-- title:
--   Original varying-grid stopped true martingale is integrable and centred at exact source ruin-truncated time
-- statement:
--   For the original X and dividend control D, every sampled ceiling index is an actual bounded stopping time for its own source right-continuous filtration. Combined with genuinely centred original true-martingale samples, pathwise upper-clock convergence, almost-everywhere right-continuity, measurability and one integrable envelope, the value at the exact min(ruinTime,n).toNNReal is Integrable and has expectation zero. All hypotheses are explicit and source exact.
-- source:
--   Proved P4-E varying-grid optional-stopping mean and exact original upper-clock dominated L1 passage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_varying_grid_stopped_martingale_sampled_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_upper_clock_rightcont_centred_L1_limit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine source martingale optional stopping and uniform domination give a centred integrable value at the exact ruin clock. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_true_grid_martingale_exact_clock_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Martingale f 𝓕.rightCont P)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (𝓖 : ℕ → Filtration ℕ mΩ)
    (h𝓖 : ∀ k, 𝓖 k =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e k i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he k hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e k i) } : Filtration ℕ mΩ))
    (hSF : ∀ k, SigmaFiniteFiltration P (𝓖 k))
    (K : ℕ → Ω → ℕ)
    (hK : ∀ k, IsStoppingTime (𝓖 k) (fun ω => (K k ω : WithTop ℕ)))
    (N : ℕ → ℕ) (hN : ∀ k ω, K k ω ≤ N k)
    (hClock : ∀ ω, Tendsto (fun k => e k (K k ω))
      atTop (𝓝 (τ ω)))
    (hAbove : ∀ k ω, τ ω ≤ e k (K k ω))
    (hRight : ∀ᵐ ω ∂P,
      ContinuousWithinAt (fun t => f t ω) (Set.Ici (τ ω)) (τ ω))
    (hMkMeas : ∀ k, AEStronglyMeasurable
      (fun ω => f (e k (K k ω)) ω) P)
    (hMMeas : AEStronglyMeasurable (fun ω => f (τ ω) ω) P)
    (B : Ω → ℝ) (hBint : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P,
      ‖f (e k (K k ω)) ω‖ ≤ B ω)
    (hLimitBound : ∀ᵐ ω ∂P, ‖f (τ ω) ω‖ ≤ ‖B ω‖)
    (hInit : ∀ k, (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
      (fun _ : Ω => (0 : WithTop ℕ)) ω ∂P) = 0) :
    Integrable (fun ω => f (τ ω) ω) P ∧
      (∫ ω, f (τ ω) ω ∂P) = 0 := by sorry
