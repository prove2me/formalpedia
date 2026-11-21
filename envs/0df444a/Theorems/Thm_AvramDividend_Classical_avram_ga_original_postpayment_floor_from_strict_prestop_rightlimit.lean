-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_postpayment_floor_from_strict_prestop_rightlimit
-- name    : AvramDividend.Classical.avram_ga_original_postpayment_floor_from_strict_prestop_rightlimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:27:23.954657+00:00
-- url     : https://prove2.me/theorems/f7d1dfc4-a909-40bc-8a1d-60d11bff7c39
-- title:
--   Original controlled reserve strict pre-stop floor transfers to its post-dividend right limit at an active physical-grid time
-- statement:
--   For the original riskProcess X x D and a time t strictly before the source stopping time ρ, if the risk process has a right limit Y_t=x+X_t−rightLimit D_t and is bounded below by δ at all strictly positive times before ρ, then Y_t≥δ. This also covers t=0 and zero-clock dividend jumps. It is the missing logical bridge between the source prepayment reserve floor and the postpayment clipped Hessian/martingale-difference coefficients on the original physical mesh. The requisite right-limit convergence is an explicit hypothesis and should be separately established from the original process path regularity.
-- source:
--   Original finitecap stopped Ito–Stieltjes source 0ef5d778 uses un-clipped Hessian below b; proved gb63 martingale difference coefficient uses an additional lower band cutoff. Establishing the post-dividend reserve floor before stopping is required for their equivalence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Filter Topology Set MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_postpayment_floor_from_strict_prestop_rightlimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (t ρ : ℝ≥0) (δ : ℝ) (ht : t < ρ)
    (hRight : Tendsto
      (fun u : ℝ≥0 => riskProcess X x D u ω)
      (𝓝[>] t) (𝓝 (x + X.X t ω - rightLimit D t ω)))
    (hFloor : ∀ u : ℝ≥0, 0 < u → u < ρ →
      δ ≤ riskProcess X x D u ω) :
    δ ≤ x + X.X t ω - rightLimit D t ω := by sorry
