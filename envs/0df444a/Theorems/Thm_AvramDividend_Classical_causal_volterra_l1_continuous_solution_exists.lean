-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_exists
-- name    : AvramDividend.Classical.causal_volterra_l1_continuous_solution_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:12:43.895504+00:00
-- url     : https://prove2.me/theorems/8252d9a0-b304-49c6-9081-3695da4a392e
-- title:
--   Existence of a locally bounded continuous solution for a causal L1 Volterra kernel
-- statement:
--   Let a be strictly positive and K integrable on the positive half-line. There exists a function G, continuous and locally bounded on positive times, satisfying the second-kind causal Volterra equation a G(x) + integral from zero to x of (β+K(x-s))G(s) ds = x. To prove it, define k=β+K on positive times. Choose δ>0 so that the L1 norm of k over (0,δ) is smaller than a. The causal Volterra operator is then a contraction in the sup norm on continuous functions on [0,δ], yielding a unique local fixed point with zero initial value. Extend iteratively across successive intervals of length δ, incorporating the known past as a continuous forcing term. The convolution of an L1 kernel with a bounded continuous zero extension is continuous. Compatibility at adjoining endpoints gives a global continuous solution, and compact-interval continuity yields the required local bounds. This is an intermediate child of target da994d48-ff61-4eb6-bc0c-9ac5052f1b09 and is paired with the independently published open regularity theorem 1d2a9fd6-58b3-40fb-bd99-9163de2a72a8.
-- source:
--   Classical Volterra integral equation resolvent construction by successive contractions on short intervals, using absolute continuity of the Lebesgue integral and the C([0,δ]) fixed-point theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_l1_continuous_solution_exists
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ G : ℝ → ℝ,
      ContinuousOn G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by sorry
