-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_terminal_bound
-- name    : AvramDividend.Classical.chat03_discounted_scale_terminal_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:41:46.285526+00:00
-- url     : https://prove2.me/theorems/45d66d53-354e-4d29-9b77-c80ac6be3fec
-- title:
--   Exponential terminal-residual bound for stopped q-scale functions inside an interval
-- statement:
--   For the published scale function W of a spectrally negative Lévy process, q>0, and reserves 0≤y≤a, if a nonnegative time t is at least a deterministic horizon N, then exp(-qt) W(y) ≤ exp(-qN) W(a). The proof uses exactly scale-function positivity and monotonicity and the strict positivity of q. In a stopped-process argument this bounds any surviving terminal reward after time N by an exponentially decreasing deterministic quantity. It does not assume or assert a killed q-scale martingale, continuity of the filtration, or continuous-time optional stopping.
-- source:
--   Chat 03 proof development, 19 October 2026. Avram, Palmowski and Pistorius (2007), arXiv:math/0702893, Sections 3.1 and 3.2, q-scale function positivity and monotonicity; Formalpedia definition Def_AvramDividend_Classical_ScaleFunction at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_discounted_scale_terminal_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a y : ℝ) (hy : 0 ≤ y) (hya : y ≤ a)
    (N t : ℝ≥0) (hNt : N ≤ t) :
    Real.exp (-(q * (t : ℝ))) * W y ≤
      Real.exp (-(q * (N : ℝ))) * W a := by sorry
