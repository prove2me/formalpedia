-- Prove2me | solution 1 for eq30_revenue_measurable_comp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:37:07.183053+00:00
-- url     : https://prove2.me/submissions/38828dfc-c492-489e-9040-6dd0bb6f797a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => revenue f p (fun i => X i ω) k (s ω)) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro s hs
      simp [revenue]
  | one =>
      intro s hs
      simp only [revenue]
      exact Measurable.ite (measurableSet_lt hs (hX 1))
        (measurable_const.mul hs) (measurable_const.mul (hX 1))
  | more n ih0 ih1 =>
      intro s hs
      have hbelow :
          Measurable (fun ω => revenue f p (fun i => X i ω) (n + 1) (s ω)) :=
        ih1 s hs
      have hmiddle :
          Measurable
            (fun ω => revenue f p (fun i => X i ω) (n + 1) (p (n + 1))) := by
        exact ih1 (fun _ => p (n + 1)) measurable_const
      have habove :
          Measurable
            (fun ω => revenue f p (fun i => X i ω) (n + 1)
              (s ω - X (n + 2) ω)) := by
        exact ih1 (fun ω => s ω - X (n + 2) ω)
          (hs.sub (hX (n + 2)))
      have hmiddle' :
          Measurable (fun ω =>
            (s ω - p (n + 1)) * f (n + 2) +
              revenue f p (fun i => X i ω) (n + 1) (p (n + 1))) := by
        measurability
      have habove' :
          Measurable (fun ω =>
            X (n + 2) ω * f (n + 2) +
              revenue f p (fun i => X i ω) (n + 1)
                (s ω - X (n + 2) ω)) := by
        exact ((hX (n + 2)).mul measurable_const).add habove
      have hprotection :
          MeasurableSet {ω | s ω < p (n + 1)} :=
        measurableSet_lt hs measurable_const
      have hcapacity :
          MeasurableSet {ω | s ω < p (n + 1) + X (n + 2) ω} :=
        measurableSet_lt hs (measurable_const.add (hX (n + 2)))
      simp only [revenue]
      exact Measurable.ite hprotection hbelow
        (Measurable.ite hcapacity hmiddle' habove')
