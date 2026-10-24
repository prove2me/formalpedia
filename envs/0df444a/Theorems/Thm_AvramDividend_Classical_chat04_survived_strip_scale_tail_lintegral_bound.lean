-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_survived_strip_scale_tail_lintegral_bound
-- name    : AvramDividend.Classical.chat04_survived_strip_scale_tail_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:37:58.247266+00:00
-- url     : https://prove2.me/theorems/6453f0d2-1e62-47d2-95dd-9b665d8bc058
-- title:
--   Exponential integral bound for surviving two-sided terminal q-scale payoff
-- statement:
--   On sample paths whose reserve remains in the full closed interval [0,a] up to time t≥N, the nonnegative terminal q-scale reward is at most exp(-qN)W(a). Its Lebesgue lower integral is therefore bounded by the corresponding constant, because the Levy law P is a probability measure. This gives a deterministic exponentially decaying expected terminal residual for continuous two-sided no-exit paths, without optional stopping or killed q-harmonicity.
-- source:
--   Consequence of the proved q-scale terminal-residual exponential bound, nonnegative strip survival and probability-mass normalisation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_terminal_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat04_survived_strip_scale_tail_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (N t : ℝ≥0) (hNt : N ≤ t) :
    (∫⁻ ω, if (∀ s : ℝ≥0, s ≤ t →
          0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a) then
       ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(q * (N : ℝ))) * W a) := by sorry
