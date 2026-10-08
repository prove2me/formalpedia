-- Prove2me | solution 1 for revenue_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T00:57:07.018274+00:00
-- url     : https://prove2.me/submissions/f2965b23-fd9e-4060-8ad2-3b6a5f83d367

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_random_measurable
import Theorems.Thm_revenue_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (f p : ℕ → ℝ) (hp : ∀ j, 1 ≤ j → 0 ≤ p j)
    (hXnonneg : ∀ i ω, 0 ≤ X i ω) (M : ℝ) (hM : 0 ≤ M)
    (n : ℕ) (hfare : ∀ j, 1 ≤ j → j ≤ n → |f j| ≤ M)
    (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => revenue f p (fun i => X i ω) n s) P := by
  have hmeas := revenue_random_measurable X hX f p n s
  have hbound : ∀ ω,
      ‖revenue f p (fun i => X i ω) n s‖ ≤ (n : ℝ) * M * s := by
    intro ω
    have hb := revenue_abs_bound f p (fun i => X i ω) M hM hp
      (fun i => hXnonneg i ω) n s hs hfare
    calc
      ‖revenue f p (fun i => X i ω) n s‖ =
          |revenue f p (fun i => X i ω) n s| := Real.norm_eq_abs _
      _ ≤ (n : ℝ) * M * s := hb
  have hmajorant : Integrable (fun _ : Ω => (n : ℝ) * M * s) P :=
    integrable_const _
  refine hmajorant.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  exact hbound ω
