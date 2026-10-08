-- Prove2me | solution 1 for revenue_random_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:59:13.616808+00:00
-- url     : https://prove2.me/submissions/d76c1eec-42e3-40d0-a11b-febcf091e8c3

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (f p : ℕ → ℝ) (n : ℕ) (s : ℝ) :
    Measurable (fun ω => revenue f p (fun i => X i ω) n s) := by
  have hdem : Measurable (fun ω => fun i => X i ω) :=
    measurable_pi_lambda _ hX
  exact (revenue_joint_measurable f p n).comp
    (Measurable.prodMk hdem measurable_const)
