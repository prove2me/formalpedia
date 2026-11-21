-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_subordinate_stop_fullmark_physical_true_Stieltjes_right_payment_Q_nonpos
-- name    : AvramDividend.Classical.avram_pj_original_subordinate_stop_fullmark_physical_true_Stieltjes_right_payment_Q_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T17:39:48.111686+00:00
-- url     : https://prove2.me/theorems/2dbd0f04-0b8c-4ade-bffb-8fce6879f462
-- title:
--   Genuine original subordinate stopped physical-grid right Stieltjes dividend correction nonpositive at every refinement
-- statement:
--   On the genuine original controlled spectrally negative Levy reserve with an admissible dividend strategy, the actual random clock rho subordinate to the original capped ruin horizon tau is always at most true ruin time. Consequently every original uniform physical-grid sampled and pre-ruin-filtered right-payment HJB secant loss Q_k, including the exact initial atom and zero-clock mask, is nonpositive at every refinement and every original sample path. This directly combines Proved subordinate clock ruin bound edebe535 with Proved true ruin-bounded grid right loss 48ff97fd, and matches exactly Q used in the original positive-clock compensated Ito source 8aa9d9be.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_exact_ruinbounded_truegrid_zero_mask_filtered_right_payment_Q_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_subordinate_stop_fullmark_physical_true_Stieltjes_right_payment_Q_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      ((Finset.range (k + 1)).image
        (fun i : ℕ => min
          ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
          (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      if ρ ω = 0 then 0 else ∑ t ∈ A k ω,
        Real.exp (-(q * (t : ℝ))) *
          ((rightLimit D t ω - D t ω) -
            (w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω))))
    ∀ k ω, Q k ω ≤ 0 := by sorry
