-- Prove2me | solution 1 for eq30RightSlope_measurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:43:34.104791+00:00
-- url     : https://prove2.me/submissions/035f798e-21c1-436c-919d-85a8858fbb97

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30RightSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30RightSlope_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) k (s ω)) := by
  have key : ∀ k, (∀ s : Ω → ℝ, Measurable s →
      Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) k (s ω))) ∧
      (∀ s : Ω → ℝ, Measurable s →
      Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) (k + 1) (s ω))) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun s _ => ?_, fun s hs => ?_⟩
      · simp only [eq30RightSlope]
        exact measurable_const
      · show Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) 1 (s ω))
        simp only [eq30RightSlope]
        exact Measurable.ite (measurableSet_lt hs (hX 1)) measurable_const measurable_const
    | succ k ih =>
      refine ⟨ih.2, fun s hs => ?_⟩
      show Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) (k + 2) (s ω))
      simp only [eq30RightSlope]
      exact Measurable.ite (measurableSet_lt hs measurable_const) (ih.2 s hs)
        (Measurable.ite (measurableSet_lt hs (measurable_const.add (hX _))) measurable_const
          (ih.2 _ (hs.sub (hX _))))
  exact fun k s hs => (key k).1 s hs

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) k (s ω)) := by
  have key : ∀ k, (∀ s : Ω → ℝ, Measurable s →
      Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) k (s ω))) ∧
      (∀ s : Ω → ℝ, Measurable s →
      Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) (k + 1) (s ω))) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun s _ => ?_, fun s hs => ?_⟩
      · simp only [eq30RightSlope]
        exact measurable_const
      · show Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) 1 (s ω))
        simp only [eq30RightSlope]
        exact Measurable.ite (measurableSet_lt hs (hX 1)) measurable_const measurable_const
    | succ k ih =>
      refine ⟨ih.2, fun s hs => ?_⟩
      show Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) (k + 2) (s ω))
      simp only [eq30RightSlope]
      exact Measurable.ite (measurableSet_lt hs measurable_const) (ih.2 s hs)
        (Measurable.ite (measurableSet_lt hs (measurable_const.add (hX _))) measurable_const
          (ih.2 _ (hs.sub (hX _))))
  exact fun k s hs => (key k).1 s hs


