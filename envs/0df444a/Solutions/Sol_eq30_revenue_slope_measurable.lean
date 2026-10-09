-- Prove2me | solution 1 for eq30_revenue_slope_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:18:52.735989+00:00
-- url     : https://prove2.me/submissions/67672a98-009f-4bc1-8fa1-0b618d50cf9e

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_eq30_revenue_measurable_comp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (k : ℕ) (s t : ℝ) :
    Measurable (fun ω =>
      slope (fun y => revenue f p (fun i => X i ω) k y) s t) := by
  have hRt : Measurable (fun ω => revenue f p (fun i => X i ω) k t) :=
    eq30_revenue_measurable_comp f p X hX k (fun _ => t) measurable_const
  have hRs : Measurable (fun ω => revenue f p (fun i => X i ω) k s) :=
    eq30_revenue_measurable_comp f p X hX k (fun _ => s) measurable_const
  dsimp [slope]
  measurability
