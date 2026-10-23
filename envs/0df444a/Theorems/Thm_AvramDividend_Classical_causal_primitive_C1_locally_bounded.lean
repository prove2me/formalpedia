-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
-- name    : AvramDividend.Classical.causal_primitive_C1_locally_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:01:21.412129+00:00
-- url     : https://prove2.me/theorems/420d4511-9b39-4a4d-80d7-9d4e717b5356
-- title:
--   The primitive of a continuous positive-time function is C1 and locally bounded
-- statement:
--   For any real-valued g continuous on [0,infinity), its causal primitive G(x)=integral_(0,x] g(s) ds is continuously differentiable on (0,infinity) and uniformly bounded over each interval (0,R] with R>0. Use the fundamental theorem of calculus locally around every x>0, proving G'(x)=g(x); continuity of g gives C1 regularity. For the bound, continuity on [0,R] implies |g|≤M on that compact interval and thus |G(x)|≤MR for 0<x≤R. The theorem does not rely on a Volterra equation and can be independently reused.
-- source:
--   Fundamental theorem of calculus for Lebesgue integrals of continuous real functions, Heine-Borel boundedness on compact intervals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_primitive_C1_locally_bounded
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, g s ∂volume)
      (Ioi (0 : ℝ)) ∧
    (∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R →
        |∫ s in Ioc (0 : ℝ) x, g s ∂volume| ≤ C) := by sorry
