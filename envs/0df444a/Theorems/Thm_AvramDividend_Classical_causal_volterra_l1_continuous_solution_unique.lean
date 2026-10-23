-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique
-- name    : AvramDividend.Classical.causal_volterra_l1_continuous_solution_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:58:22.322255+00:00
-- url     : https://prove2.me/theorems/9a0335c9-bcad-4664-bdca-ada1835c74ab
-- title:
--   Uniqueness of locally bounded continuous solutions to a causal Volterra equation
-- statement:
--   Two continuous, locally bounded positive-half-line solutions of the same positive-leading-coefficient Volterra convolution equation with an L1 causal kernel coincide. On sufficiently short intervals, the homogeneous difference has norm at most a contraction constant times its supremum. Extend from the origin stepwise. This requires local boundedness near zero and no differentiability of the kernel.
-- source:
--   Volterra integral equation uniqueness via Young's inequality and local L1 contraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_l1_continuous_solution_unique
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (V G : ℝ → ℝ)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hGc : ContinuousOn G (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hGb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hGe : ∀ x : ℝ, 0 < x →
      a * G x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * G s ∂volume) = x) :
    ∀ x : ℝ, 0 < x → V x = G x := by sorry
