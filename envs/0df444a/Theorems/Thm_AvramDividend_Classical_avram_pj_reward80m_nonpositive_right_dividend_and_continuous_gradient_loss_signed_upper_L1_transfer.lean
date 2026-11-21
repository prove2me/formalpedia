-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80m_nonpositive_right_dividend_and_continuous_gradient_loss_signed_upper_L1_transfer
-- name    : AvramDividend.Classical.avram_pj_reward80m_nonpositive_right_dividend_and_continuous_gradient_loss_signed_upper_L1_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:32:06.668719+00:00
-- url     : https://prove2.me/theorems/8c1483e5-2e43-44df-ad1f-fa02527d7c49
-- title:
--   True original nonpositive dividend gradient loss may be discarded from signed upper L1 Ito residual without absolute convergence of complete loss
-- statement:
--   In the genuine controlled stopped stochastic Ito ledger, if the HJB gap V-U is bounded above by a small integrable spatial error K, a nonpositive right-payment/continuous-gradient loss Q_k, and an integrable upper stochastic mesh error E_k whose absolute expected value vanishes, then the expected positive reward excess is at most epsilon/2. This is valid while the complete residual V-U-K-Q_k can have a persistent negative dividend loss, so it does not falsely require absolute L1 convergence of that full residual. Follows from Proved original signed upper L1 transfer cb4c3330.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80m_nonpositive_right_dividend_and_continuous_gradient_loss_signed_upper_L1_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G U V : Ω → ℝ) (Q : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∀ᵐ ω ∂P,
        V ω - U ω ≤ K ω + Q k ω + E k ω) ∧
      Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hQ : ∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by sorry
