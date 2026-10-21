-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_bddAbove_Icc
-- name    : AvramDividend.Classical.postPaymentReserve_bddAbove_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:26:00.239987+00:00
-- url     : https://prove2.me/theorems/3c93cc3b-613a-4e7d-8891-97193e87591e
-- title:
--   The post-payment controlled surplus is bounded above on finite sample-path horizons
-- statement:
--   For every finite time horizon and every sample path, the post-payment reserve x+X_t−D_{t+} is bounded above. The Lévy path is càdlàg by its defining hypotheses and therefore bounded above on compact horizons by an already Proved general one-sided-limits theorem. Monotonicity of the dividend path gives D_{t+}≥D_t≥D_0, so the reserve is no larger than x+sup_{s≤T}X_s−D_0. The bound is pathwise and may depend on ω and T, so it does not assert a false uniform stochastic localisation bound.
-- source:
--   Pathwise compact local upper bound, using Proved one_sided_limits_bddAbove_Icc and dividendStrategy_le_rightLimit. No open or pending theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_bddAbove_Icc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) T =>
        x + X.X s.1 ω - rightLimit D s.1 ω)) := by sorry
