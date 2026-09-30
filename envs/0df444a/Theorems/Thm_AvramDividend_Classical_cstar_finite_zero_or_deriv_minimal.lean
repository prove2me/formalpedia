-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_zero_or_deriv_minimal
-- name    : AvramDividend.Classical.cstar_finite_zero_or_deriv_minimal
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T23:31:55.015089+00:00
-- url     : https://prove2.me/theorems/ee428038-3735-472d-a30b-5fd6a61440fa
-- title:
--   The finite barrier c* is zero or a global minimiser of the scale-function derivative
-- statement:
--   Under the standing assumptions, c* is finite. If its real value is positive, continuity of W' closes the infimum in the definition of c*: c* itself is a global minimiser of W' over (0,∞). Otherwise c*=0.
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, definition (5.2), Lemma 2(i), and Lemma 3(i), whose proof states that after c*<infinity the derivative bound follows from the definition of c*; continuity is supplied by condition (3.3).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem cstar_finite_zero_or_deriv_minimal {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ((cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) := by sorry

end AvramDividend.Classical
