-- Prove2me | Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity
-- name    : AvramDividend.Classical.two_sided_exit_before_ruin_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T20:26:39.968869+00:00
-- url     : https://prove2.me/theorems/5bcf90e1-211c-42db-beac-d92aeb95b5c9
-- title:
--   Two-sided exit identity before ruin
-- statement:
--   For a spectrally negative Lévy process started from x in [0,a], the expected discount factor at the upward exit from [0,a], restricted to the event that the upward exit occurs before the first downward exit below 0, equals W^(q)(x)/W^(q)(a). Unlike the older one-sided exit target, this statement includes the ruin/downward-exit event required by equation (3.6).
-- source:
--   Avram, Palmowski and Pistorius, arXiv:math/0702893v1, equation (3.6) and Proposition 1, pp. 6-8. Equation (3.6) is explicitly a two-sided exit identity with indicator {T^-_0 > T^+_a}; Proposition 1 uses that event in the strong-Markov factorisation of the barrier value.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

noncomputable def twoSidedExitUpTime
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)

noncomputable def twoSidedExitDownTime
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : X.X t ω < b), (t : ℝ≥0∞)

noncomputable def twoSidedExitExpectation
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω,
    if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
    else 0 ∂P

end AvramDividend.Classical

namespace AvramDividend.Classical

theorem two_sided_exit_before_ruin_identity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by sorry

end AvramDividend.Classical
