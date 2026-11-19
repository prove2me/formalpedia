-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_ruin_contact_rational_final_strict_cash_tail_vanish
-- name    : AvramDividend.Classical.avram_f6_original_ruin_contact_rational_final_strict_cash_tail_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:26:59.448378+00:00
-- url     : https://prove2.me/theorems/cd192067-fdc0-4a0e-b85f-36db55a43272
-- title:
--   Actual original ruin contact discounted strict cash in rational shrinking last mesh interval tends to zero
-- statement:
--   For the authentic spectrally negative Lévy ruin time and original dividend strategy D, the discounted Stieltjes cash on the strict final contact interval (T-1/(n+1),T), restricted to original paymentTimes(ruinTime), tends to zero as n increases. This directly discharges the strictly-pre-contact terminal mesh cash tail in the original stopped mixed process, with any random realised T but no false restriction that dividend measures have no atoms at T, since the final interval is open at T. It applies to the original full dividend measure and does not assume the positive-clock Itô budget.
-- source:
--   Proved original strict crossing cell discounted cash tail 28ff0f1f and pinned Mathlib scalar inverse rational limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_ruin_contact_rational_final_strict_cash_tail_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun n : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((T : ℝ) - 1 / ((n : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
