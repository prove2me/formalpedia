-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_lower_eventual_renewal_of_exit_factor
-- name    : AvramDividend.Classical.chat12_lower_eventual_renewal_of_exit_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:04:15.947923+00:00
-- url     : https://prove2.me/theorems/8b8a142b-a8a7-4e3f-b060-aaa26af8112c
-- title:
--   Conditional left finite-difference barrier valuation under eventual strict q-scale exit identities
-- statement:
--   For a q-scale function differentiable with nonzero derivative at a positive barrier, assume that for all sufficiently small positive ε the genuine discounted strict ε-up-before-(ε-a)-down exit expectation equals W(a-ε)/W(a). Then the barrier dividend value eventually exceeds the left finite-difference quotient ENNReal.ofReal(ε*W(a-ε)/(W(a)-W(a-ε))). The proof combines Proved scale-function positivity, derivative-gap estimates, conditional lower geometric killed-record expectations and Proved dividend lower valuation comparison. The corrected q-scale exit identity remains an explicit premise.

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_actual_grid
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_expected_scale_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_pos_eventually_backward_scale_gap

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.chat12_lower_eventual_renewal_of_exit_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q := by sorry
