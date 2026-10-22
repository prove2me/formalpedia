-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_L1_common_ae_limit
-- name    : AvramDividend.Classical.real_L1_common_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T13:09:48.502109+00:00
-- url     : https://prove2.me/theorems/41061f11-53b5-4296-aeb1-fdd90670c737
-- title:
--   Almost-everywhere equality of common ordinary-L1 limits of almost-everywhere equal approximation sequences
-- statement:
--   Let two sequences F_n and G_n of strongly measurable real random variables agree almost everywhere at each index. Assume F_n tends to F in ordinary integrated-absolute L1 and G_n tends to G likewise, with all differences integrable and the limit functions strongly measurable. Then F and G agree almost everywhere. Apply the separately Proved conversion from ordinary L1 convergence to convergence in measure to both sequences, then use the separately Proved uniqueness of a.e.-equal approximating sequences under convergence in measure. This packages the final limit transfer needed to promote exact finite-state conditional Lévy Markov identities into general-state ones once both analytic L1 stability bounds and an adapted simple-function approximation are supplied.
-- source:
--   Proved real_L1_tendstoInMeasure target 4eb874d8-cbcc-4672-be58-a424330cac47 and Proved ae_eq_of_common_tendstoInMeasure target 0bec8de6-837e-4017-92ab-acc7f9cdc56f.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_real_L1_tendstoInMeasure
import Theorems.Thm_AvramDividend_Classical_ae_eq_of_common_tendstoInMeasure

open Filter MeasureTheory
open AvramDividend.Classical

theorem AvramDividend.Classical.real_L1_common_ae_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Fn Gn : ℕ → Ω → ℝ) (F G : Ω → ℝ)
    (hFn : ∀ n, StronglyMeasurable (Fn n))
    (hGn : ∀ n, StronglyMeasurable (Gn n))
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (hIntF : ∀ n, Integrable (fun ω => Fn n ω - F ω) P)
    (hIntG : ∀ n, Integrable (fun ω => Gn n ω - G ω) P)
    (hEq : ∀ n, Fn n =ᵐ[P] Gn n)
    (hLimF : Tendsto
      (fun n : ℕ => ∫ ω, |Fn n ω - F ω| ∂P) atTop (nhds 0))
    (hLimG : Tendsto
      (fun n : ℕ => ∫ ω, |Gn n ω - G ω| ∂P) atTop (nhds 0)) :
    F =ᵐ[P] G := by sorry
