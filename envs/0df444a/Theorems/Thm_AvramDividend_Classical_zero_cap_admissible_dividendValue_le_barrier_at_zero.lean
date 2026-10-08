-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
-- name    : AvramDividend.Classical.zero_cap_admissible_dividendValue_le_barrier_at_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T17:55:59.684433+00:00
-- url     : https://prove2.me/theorems/570b5248-37cd-45e1-a600-cb46bf273fae
-- title:
--   Every zero-capped strategy from zero is dominated by reflection at zero
-- statement:
--   Starting from zero under reserve cap zero, any admissible strategy must keep the controlled surplus at zero throughout its pre-ruin lifetime. Because the underlying Lévy process has no positive jumps, the minimal regulator is the running-supremum reflection used by the zero barrier. Admissibility prevents an additional dividend jump while the reserve is zero; any attempted over-regulation causes ruin and cannot increase the discounted pre-ruin dividend measure. Hence every zero-capped strategy has value at most the zero-barrier strategy.
-- source:
--   Degenerate C=0 case underlying Avram, Palmowski and Pistorius (2007), Theorem 2(i). This is the pathwise zero-cap verification fact omitted by Proposition 4(i), whose stated range is C in (0,infinity].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem zero_cap_admissible_dividendValue_le_barrier_at_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D) :
    dividendValue X q 0 D ≤
      dividendValue X q 0 (barrierStrategy X 0 0) := by
  sorry

end AvramDividend.Classical
