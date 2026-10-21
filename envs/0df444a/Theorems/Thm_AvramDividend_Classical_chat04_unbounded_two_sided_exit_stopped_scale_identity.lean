-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
-- name    : AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T04:39:27.273827+00:00
-- url     : https://prove2.me/theorems/aed50a34-200b-4736-a369-5ae8473e3258
-- title:
--   Stopped q-scale martingale identity at the first two-sided exit, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. For 0 <= x <= a, stop the discounted q-scale payoff at the first upward passage of the level a - x or the first downward passage below -x. On a downward exit the payoff vanishes, because the scale function is zero on negative arguments. On a successful upward exit there is no positive overshoot, by the negativity of the jumps, so the stopped payoff is exactly the scale value W(a). Optional stopping at that exit therefore identifies the discounted probability of a successful upward exit, multiplied by W(a), with the initial scale value W(x). No standing assumption is required: the q-scale semigroup harmonicity that makes the discounted payoff a martingale, and the integrability of the fixed-time scale payoff that it needs, are both available for unbounded variation without the standing integrability of the process increment.
-- source:
--   The stopped q-scale martingale identity of Avram, Palmowski and Pistorius (2007), equation (3.6), in the unbounded-variation case. The standing-case version is the Open theorem two_sided_exit_stopped_scale_identity; the semigroup harmonicity and the fixed-time integrability it needs are the Proved theorems chat04_unbounded_past_event_scale_condExp and chat04_unbounded_scale_fixed_time_integrable. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
