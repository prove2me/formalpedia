-- Prove2me | Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
-- name    : AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T20:43:16.943739+00:00
-- url     : https://prove2.me/theorems/3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7
-- title:
--   Two-sided exit identity before ruin without local helper definitions
-- statement:
--   For a spectrally negative Lévy process started from x in [0,a], the discounted upward exit expectation restricted to upward exit before downward ruin equals W^(q)(x)/W^(q)(a). The stopping times are written directly in the theorem so the target has no local preamble definitions.
-- source:
--   Avram, Palmowski and Pistorius, arXiv:math/0702893v1, equation (3.6) and Proposition 1, pp. 6-8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem two_sided_exit_before_ruin_integral_identity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by sorry

end AvramDividend.Classical
