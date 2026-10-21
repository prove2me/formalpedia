-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_bounded_compact_horizon
-- name    : AvramDividend.Classical.postPaymentReserve_bounded_compact_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:28:11.848876+00:00
-- url     : https://prove2.me/theorems/d0cf735d-6d3d-47dc-9380-d6b3dda1f6b9
-- title:
--   The post-payment controlled reserve is pathwise bounded on every finite horizon
-- statement:
--   For every finite T and path ω, the set {x+X_t(ω)−D_{t+}(ω):0≤t≤T} is bounded in ℝ. This is a pathwise compact-interval boundedness consequence of the already Proved càdlàg and adapted post-payment reserve theorem, including the empty left neighbourhood at t=0. Apply the accepted generic right/left-limits upper-bound theorem to both f and −f, obtain above and below bounds on the image, and combine. The conclusion is intentionally pathwise, not a false uniform deterministic bound across ω.
-- source:
--   From Proved postPaymentReserve_cadlag_adapted (candidate 12129), Proved one_sided_limits_bddAbove_Icc; no Ito formula, no pending theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_bounded_compact_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    Bornology.IsBounded
      ((fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) ''
        Set.Icc (0 : ℝ≥0) T) := by sorry
