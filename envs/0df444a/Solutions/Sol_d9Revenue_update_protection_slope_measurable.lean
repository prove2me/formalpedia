-- Prove2me | solution 1 for d9Revenue_update_protection_slope_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:32:03.014974+00:00
-- url     : https://prove2.me/submissions/fa9016e0-6dfc-41c1-9f0e-b0d4a1d41b57

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_measurable_comp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (j n : ℕ) (s a b : ℝ) :
    Measurable (fun ω => slope
      (fun u => revenue f (Function.update p j u) (fun i => X i ω) n s) a b) := by
  have hFa : Measurable (fun ω =>
      revenue f (Function.update p j a) (fun i => X i ω) n s) :=
    d9Revenue_measurable_comp f (Function.update p j a) X hX n
      (fun _ => s) measurable_const
  have hFb : Measurable (fun ω =>
      revenue f (Function.update p j b) (fun i => X i ω) n s) :=
    d9Revenue_measurable_comp f (Function.update p j b) X hX n
      (fun _ => s) measurable_const
  dsimp [slope]
  measurability
