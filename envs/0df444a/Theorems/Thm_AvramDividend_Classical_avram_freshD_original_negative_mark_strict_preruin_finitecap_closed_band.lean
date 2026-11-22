-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_negative_mark_strict_preruin_finitecap_closed_band
-- name    : AvramDividend.Classical.avram_freshD_original_negative_mark_strict_preruin_finitecap_closed_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T09:23:26.595894+00:00
-- url     : https://prove2.me/theorems/cecbcbd6-0208-4b39-86b8-52a337b7f4c6
-- title:
--   Every genuine negative Lévy jump strictly before ruin has predictable reserve in (0,C] under the original finite cap
-- statement:
--   For the original spectrally negative Lévy path and actual original finite-cap admissible dividend strategy, every strictly pre-ruin negative Lévy source jump at positive physical time t has a predictable controlled prestate x+X(t-)-D(t) strictly positive and at most C.toReal using the original root initial-cap condition ENNReal.ofReal x ≤ C. Strict positivity follows because postmark controlled reserve is nonnegative before ruin and the true mark is negative. The cap bound follows from the already-Proved original shifted postright reserve leftLimit cap estimate with shift zero and the exact postpayment premark leftLim identity. The boundary Y=C is deliberately retained: the source cannot invoke a C² HJB inequality there without a separate cap-contact null mark argument. For C=TOP this theorem does not apply.
-- source:
--   Original cap exact proof uses accessible Proved a009975c, exact postright leftLimit 06dc12b5, strict negative mark Y>0 47e717a5, and canonical original hxc from root 242ca5f1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_strict_preruin_negative_mark_prestate_positive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_negative_mark_strict_preruin_finitecap_closed_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hFin : C ≠ ⊤) (hxc : ENNReal.ofReal x ≤ C)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (htpos : 0 < t)
    (htpreruin : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hz : X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t < 0) :
    0 < x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ∧
    x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ≤ C.toReal := by sorry
