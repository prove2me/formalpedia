-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_C1_solution_exists
-- name    : AvramDividend.Classical.causal_volterra_l1_C1_solution_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T10:58:22.255422+00:00
-- url     : https://prove2.me/theorems/da994d48-ff61-4eb6-bc0c-9ac5052f1b09
-- title:
--   C1 resolvent existence for locally integrable causal Volterra kernels
-- statement:
--   For a>0 and a causal convolution kernel K integrable on positive times, there is a continuously differentiable solution G of aG(x)+integral_0^x (β+K(x-s))G(s) ds=x; moreover G is uniformly bounded on each bounded positive interval. Prove by local contraction of the Volterra operator, using the small L1 norm of K on short intervals, and extend the solution successively. The identity G=∫g where g is the causal resolvent of 1 yields C1 regularity.
-- source:
--   Classical Volterra equations of second kind, local L1 convolution contraction and resolvent series.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_l1_C1_solution_exists
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by sorry
