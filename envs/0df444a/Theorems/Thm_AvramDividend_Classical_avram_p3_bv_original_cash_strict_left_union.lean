-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_left_union
-- name    : AvramDividend.Classical.avram_p3_bv_original_cash_strict_left_union
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:46:13.98913+00:00
-- url     : https://prove2.me/theorems/1f3076c3-7c16-4e6f-b877-394759e61e51
-- title:
--   Exact original strict-horizon payment set is the union of cofinal earlier cutoff payment sets
-- statement:
--   For the same original risk process, ruin time and complete Stieltjes paymentTimes, the payment times strictly before T equal the union of payment sets cut off by an arbitrary family of earlier cutoffs cofinal below T. This is a deterministic source-exact measure-continuity interface preserving all earlier atoms and excluding the right-payment at T.
-- source:
--   Exact set extensionality, paymentTimes and original ruinTime; no new mathematical hypothesis on X beyond those in the original formal definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_cash_strict_left_union
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (u : ℕ → ℝ)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    (⋃ n, paymentTimes (ruinTime X x D ω) ∩ Iio (u n)) =
      paymentTimes (ruinTime X x D ω) ∩ Iio T := by sorry
