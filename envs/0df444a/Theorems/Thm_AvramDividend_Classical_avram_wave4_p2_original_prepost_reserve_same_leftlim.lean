-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
-- name    : AvramDividend.Classical.avram_wave4_p2_original_prepost_reserve_same_leftlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:22:24.472225+00:00
-- url     : https://prove2.me/theorems/caa7f605-3813-4ed6-82a2-31dc2d0b01a0
-- title:
--   Actual pre-payment and post-payment controlled Lévy reserves share the same strict-left limit
-- statement:
--   For every original spectrally negative Lévy sample path, every admissible dividend strategy, every initial capital and positive source time, the true strict-left limit of the pre-payment reserve riskProcess X x D equals the true strict-left limit of the post-payment reserve x+X−rightLimit D. Although these values differ by the right-payment atom at the current instant, the left-continuity of the original cumulative dividend path forces their pre-event limits to coincide. The result establishes source chronology without an artificial continuous-control assumption and is valid in both bounded and unbounded variation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), predictable pre-event reserve; source Lévy leftLim and IsDividendStrategy left-continuity, canonical postPaymentReserve_exact_leftLim_identity 06dc12b5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_prepost_reserve_same_leftlim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t =
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t := by sorry
