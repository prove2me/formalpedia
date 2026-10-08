-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
-- name    : AvramDividend.Classical.vcstar_basic_boundary_regular_of_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T20:48:09.520979+00:00
-- url     : https://prove2.me/theorems/c6167930-c245-49bf-a03b-7af5826dbf00
-- title:
--   Basic continuity and boundary properties of the positive c-star candidate
-- statement:
--   For a positive finite c*, the candidate value function vcstar is continuous on [0,∞), is nonnegative at the origin, and agrees with the formal zero extension on the negative half-line. These are the elementary boundary properties needed by Proposition 4(i), separated from the higher-order smoothness and generator arguments.
-- source:
--   Avram, Palmowski and Pistorius (2007), definition (5.1), scale-function continuity in Section 3.2 and Proposition 4(i), pp. 5, 13 and 18. Elementary piecewise-analysis bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem vcstar_basic_boundary_regular_of_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      ∀ y < 0, vcstar W y = 0 := by
  sorry

end AvramDividend.Classical
