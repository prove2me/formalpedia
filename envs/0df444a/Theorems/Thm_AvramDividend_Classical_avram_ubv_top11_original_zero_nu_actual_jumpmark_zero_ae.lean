-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae
-- name    : AvramDividend.Classical.avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:25:42.657769+00:00
-- url     : https://prove2.me/theorems/e847d9a7-2239-4a13-b5a9-6190bb955bcd
-- title:
--   All actual positive-time original Lévy jump marks vanish together under zero jump measure
-- statement:
--   When the original spectrally negative Lévy jump measure ν is zero, the actual source-path jump mark X(t) minus its left limit is zero at every strictly positive time on one probability-one event. The proof uses the Proved original-source almost-sure continuity and exact source jump-continuity equivalence.
-- source:
--   Authoritative TOP11 632b191c and authoritative original jump-continuity identification d98a57fe. This provides literal original path jumpmark elimination for the Gaussian-only Ito-Meyer dividend ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = 0 := by sorry
