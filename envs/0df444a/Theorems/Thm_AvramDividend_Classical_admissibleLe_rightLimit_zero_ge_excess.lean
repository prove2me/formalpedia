-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissibleLe_rightLimit_zero_ge_excess
-- name    : AvramDividend.Classical.admissibleLe_rightLimit_zero_ge_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:20:39.712599+00:00
-- url     : https://prove2.me/theorems/bfa9f4a8-fc16-4a16-92d2-004ae022885b
-- title:
--   A capped admissible strategy must remove the initial excess at time zero
-- statement:
--   If a dividend strategy started from x is admissible under a finite reserve cap c with 0≤c<x, then its right limit of cumulative dividends at time zero is at least x-c on every path. Thus the excess initial capital above the cap must be removed immediately.
-- source:
--   Source-neutral consequence of the formal definition of Π_{≤C}: the controlled reserve is bounded by c at every positive time, X is right-continuous with X_0=0, and D is nondecreasing with right limit D_{0+}. If D_{0+}<x-c, sufficiently small positive times would have reserve strictly above c, contradicting the cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem admissibleLe_rightLimit_zero_ge_excess {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c) (hcx : c < x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    ∀ ω, x - c ≤ rightLimit D 0 ω := by sorry

end AvramDividend.Classical
