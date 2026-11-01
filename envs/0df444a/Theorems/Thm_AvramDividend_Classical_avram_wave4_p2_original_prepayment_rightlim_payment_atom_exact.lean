-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_rightlim_payment_atom_exact
-- name    : AvramDividend.Classical.avram_wave4_p2_original_prepayment_rightlim_payment_atom_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:36:35.604611+00:00
-- url     : https://prove2.me/theorems/948e3f54-ae6e-4914-80b1-31ddf06c5659
-- title:
--   Actual Lévy pre-payment reserve right limit equals post-payment reserve, with right jump support exactly dividend atoms
-- statement:
--   For any actual spectrally negative Lévy source path, any admissible original dividend strategy and every t≥0 (including immediate payment at zero), the strict right limit of the pre-payment reserve riskProcess equals the post-payment reserve x+X_t−D_{t+}. Consequently riskProcess has a discontinuity to the right precisely at those and only those times where the dividend cumulative strategy has a nonzero right-payment atom. Original Lévy source marks cannot create right discontinuity because the source path is right-continuous. This is the time-direction dual to the already accepted left-jump source mark identities and is a direct BV/UBV source interface for the stopped Itô–Meyer dividend jump budget.
-- source:
--   Avram–Palmowski–Pistorius (2007), source controlled reserve pre-/postpayment conventions and Proposition 4(i) verification. Canonical genuine source riskProcess_tendsto_postPaymentReserve_right 2dc41f6c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_prepayment_rightlim_payment_atom_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    Function.rightLim (fun s : ℝ≥0 => riskProcess X x D s ω) t =
      x + X.X t ω - rightLimit D t ω ∧
    (Function.rightLim (fun s : ℝ≥0 => riskProcess X x D s ω) t ≠
      riskProcess X x D t ω ↔
      rightLimit D t ω ≠ D t ω) := by sorry
