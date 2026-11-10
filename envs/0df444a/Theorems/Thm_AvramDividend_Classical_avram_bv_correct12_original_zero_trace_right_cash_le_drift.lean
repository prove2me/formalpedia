-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_original_zero_trace_right_cash_le_drift
-- name    : AvramDividend.Classical.avram_bv_correct12_original_zero_trace_right_cash_le_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:42:31.478387+00:00
-- url     : https://prove2.me/theorems/e4807977-6fdb-4091-9b23-62105a3b0bff
-- title:
--   Original BV right-dividend cash is drift dominated between arbitrary zero-reserve contacts
-- statement:
--   For the original bounded-variation Levy reserve and genuine right-limit dividends, cash paid between any pair of times whose postpayment reserves are both zero is bounded by the physical premium drift times elapsed time. This is simultaneous for all endpoint pairs, and needs neither finite jump intensity nor a zero interval. It applies, in particular, to disconnected zero-contact sets such as positive-measure fat Cantor sets, although control of Stieltjes cash concentrated at isolated zero contacts requires a further atom argument.
-- source:
--   Necessary original BV zero-reserve occupation component for source 8271cf4d, parent 3993433e and assigned 51b72610. Proved f6cc1059 supplies monotonicity of the original physical drift deficit at all times; subtract the two exact postpayment zero-reserve identities.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_original_zero_trace_right_cash_le_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      x + X.X s ω - rightLimit D s ω = 0 →
      x + X.X t ω - rightLimit D t ω = 0 →
      rightLimit D t ω - rightLimit D s ω ≤
        ((t : ℝ) - (s : ℝ)) * X.drift := by sorry
