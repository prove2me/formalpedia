-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_cstar_admissible
-- name    : AvramDividend.Classical.barrierStrategy_cstar_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:10:20.516142+00:00
-- url     : https://prove2.me/theorems/abfe3c85-92ca-49c8-be2d-905a62b70f30
-- title:
--   The finite c* barrier strategy is capped-admissible for every nonnegative initial surplus
-- statement:
--   Let c* be finite. For every initial surplus x>=0, the constant barrier strategy at c* is an admissible dividend strategy and its controlled reserve is at most c* for every positive time. For x>c* this includes the compulsory initial excess payment x-c* through the right-limit-at-zero convention. This isolates the pathwise/filtration part of Theorem 2(i): monotonicity, left continuity, adaptedness, the reserve-cap inequality and the admissibility right-limit condition.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Sections 2 and 3.3 and Theorem 2(i), pp.3-8 and 14-16.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_cstar_admissible {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (W : ℝ → ℝ) (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) := by sorry

end AvramDividend.Classical
