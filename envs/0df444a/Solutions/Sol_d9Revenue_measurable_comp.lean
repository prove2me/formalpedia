-- Prove2me | solution 1 for d9Revenue_measurable_comp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:52:04.102965+00:00
-- url     : https://prove2.me/submissions/b42e54ad-a147-4068-8d3b-d65e22bdfbfc

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
      apply Measurable.ite
      · exact measurableSet_lt hs (hX 1)
      · exact measurable_const.mul hs
      · exact measurable_const.mul (hX 1)
  | more n ih0 ih1 =>
      intro s hs
      have hbelow : Measurable (fun ω =>
          revenue f p (fun i => X i ω) (n + 1) (s ω)) := ih1 s hs
      have hmiddle : Measurable (fun ω =>
          revenue f p (fun i => X i ω) (n + 1) (p (n + 1))) :=
        ih1 (fun _ => p (n + 1)) measurable_const
      have habove : Measurable (fun ω =>
          revenue f p (fun i => X i ω) (n + 1)
            (s ω - X (n + 2) ω)) :=
        ih1 (fun ω => s ω - X (n + 2) ω) (hs.sub (hX (n + 2)))
      simp only [revenue]
      apply Measurable.ite
      · exact measurableSet_lt hs measurable_const
      · exact hbelow
      · apply Measurable.ite
        · exact measurableSet_lt hs
            (measurable_const.add (hX (n + 2)))
        · exact ((hs.sub measurable_const).mul measurable_const).add hmiddle
        · exact ((hX (n + 2)).mul measurable_const).add habove
