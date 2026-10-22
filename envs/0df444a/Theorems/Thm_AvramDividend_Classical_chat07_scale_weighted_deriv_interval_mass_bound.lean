-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_interval_mass_bound
-- name    : AvramDividend.Classical.chat07_scale_weighted_deriv_interval_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:19:18.103883+00:00
-- url     : https://prove2.me/theorems/5b20fdd6-4762-46a6-b373-f54081ec60d3
-- title:
--   Exponential-weighted scale derivative mass on each finite nonnegative interval
-- statement:
--   For every real q-scale function W, decay θ≥0 and 0≤a≤b, the product exp(-θx)·W'(x) is interval integrable on [a,b] and its integral is bounded above by exp(-θa)·(W(b)-W(a)). The proof uses the already proved nonnegative ordinary derivative of a scale function, finite-interval derivative integrability and mass, and decreasing exponential weights. No global C1, absolute continuity, or jump-free claim assumption is needed. This is a finite-interval building block for a global weighted derivative estimate used in the bounded-variation compensated Fubini problem.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_weighted_deriv_interval_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ a b : ℝ) (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
        (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x) volume a b ∧
      (∫ x in a..b, Real.exp (-(θ * x)) * deriv W x) ≤
        Real.exp (-(θ * a)) * (W b - W a) := by sorry
