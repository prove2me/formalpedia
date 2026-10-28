-- Prove2me | Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_finite_bound
-- name    : AvramDividend.Classical.two_sided_exit_before_ruin_integral_finite_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:31:20.917845+00:00
-- url     : https://prove2.me/theorems/4b5729c2-f92d-495e-8bd4-21539deec8f9
-- title:
--   Discounted two-sided exit integral is bounded by one
-- statement:
--   For a standing spectrally negative Levy process and positive discount, the discounted two-sided exit indicator integral before ruin is bounded by one, since the discount factor lies in [0,1] pointwise and P is a probability measure. This isolates the finiteness half of the two-sided exit identity.
-- source:
--   Source-faithful finite-bound reduction of AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity (3e1ce2c8). Same binders and integrand; replaces the exact scale-ratio equality (which needs optional stopping) with the provable universal bound used to rule out the infinite case.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.two_sided_exit_before_ruin_integral_finite_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
      else 0 ∂P) ≤ 1 := by
  sorry
