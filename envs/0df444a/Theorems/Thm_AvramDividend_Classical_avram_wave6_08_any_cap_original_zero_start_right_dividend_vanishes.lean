-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_any_cap_original_zero_start_right_dividend_vanishes
-- name    : AvramDividend.Classical.avram_wave6_08_any_cap_original_zero_start_right_dividend_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:09:41.47008+00:00
-- url     : https://prove2.me/theorems/fed78910-ab6c-4f14-9f83-3573d23f3e9d
-- title:
--   Original zero-capital initial dividend vanishes for every admissible cap
-- statement:
--   On the original spectrally negative Lévy probability space, any admissible dividend strategy starting from reserve zero has D(0+)=0, regardless of finite, infinite, or zero cap. Source admissibility at t=0 and the right-limit infimum imply zero payment; no stochastic or generator premise is needed. This sharpens the corrected UBV zero-initial-capital payout branch by removing the only possible zero-time atom.
-- source:
--   Exact generalization in the cap parameter of canonically Proved ce3a5c88-c022-4643-98b7-8a774b819395, accepted source 03b4cc1a-8067-4840-80ec-dc1d3b149e46; original IsAdmissibleLe definition and source X.X_zero; Chat08 independently owns zero-capital branch.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_any_cap_original_zero_start_right_dividend_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 C D) (ω : Ω) :
    rightLimit D 0 ω = 0 := by sorry
