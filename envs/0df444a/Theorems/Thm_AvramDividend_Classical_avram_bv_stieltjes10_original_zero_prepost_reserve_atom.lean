-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_zero_prepost_reserve_atom
-- name    : AvramDividend.Classical.avram_bv_stieltjes10_original_zero_prepost_reserve_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:22:35.816655+00:00
-- url     : https://prove2.me/theorems/0f54122c-c523-4b7b-ac6d-43c293ffa534
-- title:
--   Original initial prepayment reserve minus grid left-limit equals Stieltjes atom
-- statement:
--   At time zero the original reserve x-D(0) is the pre-rightpayment reserve, while the leftLimit of the rightLimit-controlled grid reserve falls back to the postpayment value x-rightLimit(D,0). Their difference is exactly the actual Stieltjes singleton measure mass, including immediate ruin.
-- source:
--   Pinned Mathlib leftLim_eq_of_isBot in Mathlib.Topology.Order.LeftRightLim, and proved original dividendMeasure singleton identity 4f229f9a; first-cell bridge into the physical signed-grid source 2bc848f9.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_stieltjes10_original_zero_prepost_reserve_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal
        (riskProcess X x D 0 ω -
          Function.leftLim
            (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) 0) := by sorry
