-- Prove2me | solution 1 for d9LeftSlope_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:01:04.989437+00:00
-- url     : https://prove2.me/submissions/22239711-9ce9-4c96-b756-ea179f40c8b9

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9LeftSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => d9LeftSlope f p (fun i => X i ω) k (s ω)) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro s hs
      simp [d9LeftSlope]
  | one =>
      intro s hs
      simp only [d9LeftSlope]
      exact Measurable.ite (measurableSet_le hs (hX 1))
        measurable_const measurable_const
  | more n ih0 ih1 =>
      intro s hs
      have hbelow : Measurable (fun ω =>
          d9LeftSlope f p (fun i => X i ω) (n + 1) (s ω)) := ih1 s hs
      have habove : Measurable (fun ω =>
          d9LeftSlope f p (fun i => X i ω) (n + 1)
            (s ω - X (n + 2) ω)) :=
        ih1 (fun ω => s ω - X (n + 2) ω) (hs.sub (hX (n + 2)))
      simp only [d9LeftSlope]
      have hbelowSet : MeasurableSet {ω | s ω ≤ p (n + 1)} :=
        measurableSet_le hs measurable_const
      have haboveSet : MeasurableSet
          {ω | s ω ≤ p (n + 1) + X (n + 2) ω} :=
        measurableSet_le hs (measurable_const.add (hX (n + 2)))
      exact Measurable.ite hbelowSet hbelow
        (Measurable.ite haboveSet measurable_const habove)
