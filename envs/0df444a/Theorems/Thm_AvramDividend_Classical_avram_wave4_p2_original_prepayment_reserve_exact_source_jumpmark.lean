-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
-- name    : AvramDividend.Classical.avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:28:03.101871+00:00
-- url     : https://prove2.me/theorems/d2800259-b627-4fd5-b139-985adba4e243
-- title:
--   Actual pre-payment controlled reserve left-jump mark is exactly the original Lévy source jump mark
-- statement:
--   For every source sample and positive time, the precise left-jump increment of the original pre-payment reserve riskProcess X x D equals the true original spectrally negative Lévy jump X_t−X_{t−} exactly, irrespective of simultaneous right-dividend payment atoms. This uses the left-continuity of D and the accepted original pre/post reserve left-limit identification; in contrast the post-payment reserve jump subtracts the right dividend atom. The identity is directly suited to the marked-jump compensator and stopped Itô–Meyer generator terms in both bounded and unbounded variation.
-- source:
--   Avram–Palmowski–Pistorius (2007), Section 2 controlled reserve jump convention and Proposition 4(i) Itô–Meyer source mark; pre/post source limit caa7f605 and 06dc12b5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    riskProcess X x D t ω -
      Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t =
      X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by sorry
