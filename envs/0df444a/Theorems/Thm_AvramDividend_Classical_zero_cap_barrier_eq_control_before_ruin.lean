-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_barrier_eq_control_before_ruin
-- name    : AvramDividend.Classical.zero_cap_barrier_eq_control_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:01:14.964524+00:00
-- url     : https://prove2.me/theorems/3deb8c8f-4539-4321-bf5f-50e32b1e6f98
-- title:
--   Zero-cap admissible dividends agree with zero-barrier reflection before ruin
-- statement:
--   Before ruin, a zero-capped admissible dividend strategy satisfies D_t=X_t. Its monotonicity therefore makes the underlying Lévy path monotone on each strict pre-ruin prefix, and the barrier supremum equals its terminal value D_t. Thus the zero barrier and the arbitrary zero-capped strategy agree before the arbitrary strategy's ruin.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.3 barrier definition and exact zero-cap strategy definitions.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_barrier_eq_control_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X 0 D ω) :
    barrierStrategy X 0 0 t ω = D t ω := by sorry
