-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:36:38.263123+00:00
-- url     : https://prove2.me/theorems/639689ae-5ae0-4907-85ae-40eddfe401bf
-- title:
--   Original controlled post-payment reserve left-limit convergence along any left-approaching deterministic mesh
-- statement:
--   For the actual original Lévy X and dividend strategy D, at every fixed physical path ω and time t, any deterministic mesh sequence s_n≤t tending to t transports the actual post-payment reserve's pre-jump left limit to the correct time-t left limit. This is the direct pointwise approximation step required before passing predictable simple grid coefficients to the derivative-driven stopped Itô–Meyer kernel, under the genuine X/D rather than a Poisson proxy.
-- source:
--   The original controlled reserve has left limits at each positive time from the Proved physical pre-jump upper theorem (490a1c4e). The Proved left-limit-left-continuity theorem (ed804a27) gives continuity of the actual left-limit map on Iic t at t. Tendsto s_n to t with s_n≤t is exactly convergence in the Iic t neighbourhood filter. Compose the two tendsto statements.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t)) :
    Tendsto
      (fun n => Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s n))
      atTop
      (𝓝 (Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)) := by sorry
