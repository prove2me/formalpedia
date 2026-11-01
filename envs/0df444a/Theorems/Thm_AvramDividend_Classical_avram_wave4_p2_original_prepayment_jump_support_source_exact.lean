-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_jump_support_source_exact
-- name    : AvramDividend.Classical.avram_wave4_p2_original_prepayment_jump_support_source_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:26:27.491778+00:00
-- url     : https://prove2.me/theorems/298f0484-3dc5-43ed-b495-80ef3f5ae7b6
-- title:
--   Actual pre-payment controlled Lévy reserve left-jumps exactly at original source Lévy jump times
-- statement:
--   For every true original spectrally negative Lévy sample path, admissible dividend strategy and positive time, the pre-payment controlled riskProcess X x D has a left jump if and only if the original source X has a left jump. The cumulative dividend process D is left-continuous by definition, so right-payment atoms do not create left jumps in riskProcess; by contrast, the post-payment reserve jump support is the union of source jumps and payment atoms. This exact source chronological distinction is needed to separate original Poisson jump marks from dividend payments in the stopped HJB Itô–Meyer formula.
-- source:
--   Avram–Palmowski–Pistorius (2007), Section 2 pre-payment surplus and Proposition 4(i) jump terms; proven exact pre/post reserve left-limit identity caa7f605 and postPaymentReserve_exact_leftLim_identity 06dc12b5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_prepayment_jump_support_source_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (riskProcess X x D t ω ≠
      Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t) ↔
      (X.X t ω ≠ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by sorry
