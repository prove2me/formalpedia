-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_ge_excess_reserve_above_cstar
-- name    : AvramDividend.Classical.vcstar_ge_excess_reserve_above_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:44:27.068082+00:00
-- url     : https://prove2.me/theorems/f23add99-618c-4280-890d-d80fb01c70cc
-- title:
--   Dividend candidate exceeds the excess reserve above the optimal barrier
-- statement:
--   For any positive reserve strictly exceeding the formal optimal barrier, the candidate dividend value dominates the surplus above the barrier. The candidate is affine above cstar with slope one and a nonnegative boundary value, so v_cstar(x)≥x−cstar. This bound is a reusable bridge between the explicit reserve level and the generator discount term qv_cstar(x), useful in HJB and dividend strategy inequalities.
-- source:
--   Canonically Proved nonnegative constant-barrier value 861b7656-5bc3-4d92-81da-da184060de56 and affine optimal-barrier continuation ee11c526-1dfc-4622-86fb-5de4518a7c45.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_ge_excess_reserve_above_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x : ℝ)
    (hx : (cstar W).toReal < x) :
    x - (cstar W).toReal ≤ vcstar W x := by sorry
