-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_control_eq_levy_before_ruin
-- name    : AvramDividend.Classical.zero_cap_control_eq_levy_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:49:04.52349+00:00
-- url     : https://prove2.me/theorems/96a8cc7b-cbf5-4d77-a028-a5ecc08f16e0
-- title:
--   Zero-cap pre-ruin controlled dividend equals Lévy reserve
-- statement:
--   For a zero-capped admissible dividend strategy started from capital zero, at each strictly positive time strictly before ruin, the entire Lévy reserve equals cumulative dividends. The zero-cap condition yields U_t≤0; the ruin-time infimum yields U_t≥0, hence U_t=0. This pathwise lemma is a substantive prerequisite for comparing an arbitrary zero-capped strategy to the zero barrier without stochastic Itô calculus.
-- source:
--   Avram, Palmowski and Pistorius (2007), dividend strategy and ruin definitions, arXiv:math/0702893, Section 2.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_control_eq_levy_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X 0 D ω) :
    D t ω = X.X t ω := by sorry
