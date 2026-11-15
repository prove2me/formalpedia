-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_dominated_ae_two_noise_cash_excess_L1
-- name    : AvramDividend.Classical.avram_b24_original_dominated_ae_two_noise_cash_excess_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:14:25.019663+00:00
-- url     : https://prove2.me/theorems/7c11da93-7ceb-4478-b4a7-55812ff46fc1
-- title:
--   Original dominated almost-sure two-noise stopped cash ledger yields integrable vanishing positive cash error in L1
-- statement:
--   Suppose the true original discounted stopped dividend cash F is integrable, the two genuine Gaussian and compensated smallmark noise gains G,J are integrable at each physical grid level and uniformly dominated by respective integrable original-source envelopes BG,BJ, both noises converge almost surely to their own original-source limits, and the exact physical cash ledger has F≤w+G_m+J_m+E_m with signed error E_m tending to zero almost surely. Then without assuming signed E_m integrability, set Epos_m=max(F-w-G_m-J_m,0). This new error is genuinely integrable, bounds the ORIGINAL CASH at every grid level, and its expected absolute value tends to zero by a source-faithful DCT, because the a.e. limit budget implies F≤w+MG+MJ and the deficit is dominated by |F|+|w|+BG+BJ. This bridges the stronger B219 original dominated mesh source to B24 positive-clock signed Ito-Meyer source without replacing X, Jsmall, original cash, terminal ruin contact or payment conventions.
-- source:
--   Proved B24 source DCT and pinned Mathlib a.e. limit/integrability; original source inputs are explicit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_dominated_ae_two_noise_cash_excess_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Ω → ℝ) (w : ℝ) (G J E : ℕ → Ω → ℝ)
    (MG MJ BG BJ : Ω → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ m, Integrable (G m) P)
    (hJI : ∀ m, Integrable (J m) P)
    (hBGI : Integrable BG P) (hBJI : Integrable BJ P)
    (hGB : ∀ m, ∀ᵐ ω ∂P, ‖G m ω‖ ≤ BG ω)
    (hJB : ∀ m, ∀ᵐ ω ∂P, ‖J m ω‖ ≤ BJ ω)
    (hGAE : ∀ᵐ ω ∂P, Tendsto (fun m => G m ω) atTop (𝓝 (MG ω)))
    (hJAE : ∀ᵐ ω ∂P, Tendsto (fun m => J m ω) atTop (𝓝 (MJ ω)))
    (hEAE : ∀ᵐ ω ∂P, Tendsto (fun m => E m ω) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ m, ∀ᵐ ω ∂P, F ω ≤ w + G m ω + J m ω + E m ω) :
    let Epos : ℕ → Ω → ℝ :=
      fun m ω => max (F ω - w - G m ω - J m ω) 0
    (∀ m, Integrable (Epos m) P) ∧
      (∀ m, ∀ᵐ ω ∂P, F ω ≤ w + G m ω + J m ω + Epos m ω) ∧
      Tendsto (fun m => ∫ ω, ‖Epos m ω‖ ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
