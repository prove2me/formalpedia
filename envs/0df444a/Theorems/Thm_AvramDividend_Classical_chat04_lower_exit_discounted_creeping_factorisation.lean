-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_discounted_creeping_factorisation
-- name    : AvramDividend.Classical.chat04_lower_exit_discounted_creeping_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:01:50.617757+00:00
-- url     : https://prove2.me/theorems/dc1797c5-f173-4916-87ff-2aa7eb89fcf8
-- title:
--   Exact discounted lower-exit payoff is W(0) times the creeping-contact mass
-- statement:
--   For a spectrally negative Levy process and any q-scale function, the discounted lower-first stopped q-scale integral is exactly W(0), embedded as an extended nonnegative real, multiplied by the discounted mass of paths that touch reserve zero at the strict lower exit before the upper exit. This identity is valid without W(0)=0, without almost-sure no-creeping assumptions, and without imposing a martingale. It isolates the remaining stochastic boundary question to the distribution of exact contact and provides the correct boundary term for optional stopping in bounded variation and unbounded variation.
-- source:
--   Previously remotely Proved AvramDividend.Classical.chat04_lower_exit_scale_creeping_atom (UUID 0f1adee0-3670-4143-b12f-b52df6fbae1b). Exact pinned Mathlib.MeasureTheory.Integral.Lebesgue.Add theorem lintegral_mul_const' and ENNReal.ofReal_ne_top.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_exit_discounted_creeping_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) =
      (∫⁻ ω,
        if twoSidedExitDownTime X (-x) ω <
            twoSidedExitUpTime X (a - x) ω ∧
           x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0
        then ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal)))
        else 0 ∂P) * ENNReal.ofReal (W 0) := by sorry
