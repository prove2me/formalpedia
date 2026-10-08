-- Prove2me | solution 1 for d9Revenue_slope_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:31:47.680821+00:00
-- url     : https://prove2.me/submissions/b16ed363-c894-461d-b1c8-33f06bc920c9

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_measurable_comp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (k : ℕ) (s t : ℝ) :
    Measurable (fun ω =>
      slope (fun y => revenue f p (fun i => X i ω) k y) s t) := by
  have hRt : Measurable (fun ω =>
      revenue f p (fun i => X i ω) k t) :=
    d9Revenue_measurable_comp f p X hX k (fun _ => t) measurable_const
  have hRs : Measurable (fun ω =>
      revenue f p (fun i => X i ω) k s) :=
    d9Revenue_measurable_comp f p X hX k (fun _ => s) measurable_const
  dsimp [slope]
  measurability
