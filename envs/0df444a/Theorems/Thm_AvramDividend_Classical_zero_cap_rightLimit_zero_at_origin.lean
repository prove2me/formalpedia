-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_rightLimit_zero_at_origin
-- name    : AvramDividend.Classical.zero_cap_rightLimit_zero_at_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:58:19.846661+00:00
-- url     : https://prove2.me/theorems/ce3a5c88-c022-4643-98b7-8a774b819395
-- title:
--   A zero-cap admissible strategy cannot pay an initial dividend from zero capital
-- statement:
--   An admissible nondecreasing left-continuous dividend control starting with zero capital has zero initial right-limit dividend. Admissibility enforces D_{0+}-D_0 ≤ U_0=0, and monotonicity forces D_{0+}≥D_0=0. This removes the time-zero Stieltjes atom in the zero-cap comparison proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 2; exact zero-time admissibility and rightLimit definitions.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_rightLimit_zero_at_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D) (ω : Ω) :
    rightLimit D 0 ω = 0 := by sorry
