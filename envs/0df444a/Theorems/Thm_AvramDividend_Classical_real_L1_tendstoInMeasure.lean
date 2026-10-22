-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_L1_tendstoInMeasure
-- name    : AvramDividend.Classical.real_L1_tendstoInMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:54:21.256476+00:00
-- url     : https://prove2.me/theorems/4eb874d8-cbcc-4672-be58-a424330cac47
-- title:
--   Ordinary integrated absolute L1 convergence implies convergence in measure
-- statement:
--   For strongly measurable real-valued functions F_n and F on any measure space, assume every difference F_n−F is integrable and the real integral of its absolute value tends to zero. Prove that F_n converges to F in measure. The proof identifies the eLpNorm at p=1 with the ENNReal-valued integral of the pointwise norm, uses ofReal_integral_norm_eq_lintegral_enorm and continuity of ENNReal.ofReal at zero, and then invokes the exact pinned Mathlib tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable theorem. This is the analytic bridge from the Chat 08 ordinary L1 approximation results to Mathlib convergence-in-measure uniqueness, allowing finite-state conditional Lévy Markov identities to be passed to integrable limits after the remaining measurability steps.
-- source:
--   Pinned eLpNorm_one_eq_lintegral_enorm, ofReal_integral_norm_eq_lintegral_enorm, ENNReal.continuous_ofReal and tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum

open Filter MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.real_L1_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Fn : ℕ → Ω → ℝ) (F : Ω → ℝ)
    (hFn : ∀ n, StronglyMeasurable (Fn n))
    (hF : StronglyMeasurable F)
    (hInt : ∀ n, Integrable (fun ω => Fn n ω - F ω) P)
    (hlim : Tendsto
      (fun n : ℕ => ∫ ω, |Fn n ω - F ω| ∂P)
      atTop (nhds 0)) :
    TendstoInMeasure P Fn atTop F := by sorry
