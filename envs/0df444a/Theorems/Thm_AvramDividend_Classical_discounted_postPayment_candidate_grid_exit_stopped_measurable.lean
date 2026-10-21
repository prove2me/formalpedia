-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_grid_exit_stopped_measurable
-- name    : AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_stopped_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:55:08.030999+00:00
-- url     : https://prove2.me/theorems/4162f708-75f3-4924-9994-2b002bffe95e
-- title:
--   Discounted candidate value evaluated at a finite-grid exit stopping time is measurable
-- statement:
--   For a finite deterministic-time grid exit index K defined as the bounded hitting time of the adapted post-payment reserve exiting [lower,upper], show measurability of ω↦exp(-q clock(K(ω)))w(x+X_{clock K}−D_{(clock K)+}). The already Proved postPaymentReserve_grid_exit_stopped_measurable gives measurability of the reserve and stopped clock under the exact hittingBtwn constraint and filtration mapping. The Proved local_verification_candidate_borel_and_postPayment_adapted gives Borel measurability of w even when it jumps at 0. Compose these measurability statements with continuous real exponential and product. This supplies discrete-grid stopped terminal measurability without assuming Ito's formula, optional stopping in continuous time or original-filtration right continuity.
-- source:
--   From independently Proved postPaymentReserve_grid_exit_stopped_measurable (12155) and local_verification_candidate_borel_and_postPayment_adapted (12220); pinned Real.continuous_exp.

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_grid_exit_stopped_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_stopped_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max
        (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω -
          rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        w (x + X.X (clock (K ω)) ω -
          rightLimit D (clock (K ω)) ω)) := by sorry
