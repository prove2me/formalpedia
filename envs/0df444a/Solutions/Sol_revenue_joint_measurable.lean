-- Prove2me | solution 1 for revenue_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:12:23.054994+00:00
-- url     : https://prove2.me/submissions/b59776c3-675f-4f7b-bb41-c3ffcf1c9aa6

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (f p : ℕ → ℝ) :
    ∀ n, Measurable
      (fun z : (ℕ → ℝ) × ℝ => revenue f p z.1 n z.2) := by
  have hgeneral : ∀ n (s : ((ℕ → ℝ) × ℝ) → ℝ), Measurable s →
      Measurable (fun z => revenue f p z.1 n (s z)) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
        intro s hs
        simp [revenue]
    | one =>
        intro s hs
        simp only [revenue]
        have hcoord_one :
            Measurable (fun z : (ℕ → ℝ) × ℝ => z.1 1) :=
          (measurable_pi_apply 1).comp measurable_fst
        have hcond : MeasurableSet {z : (ℕ → ℝ) × ℝ | s z < z.1 1} :=
          measurableSet_lt hs hcoord_one
        have hbelow : Measurable (fun z : (ℕ → ℝ) × ℝ => f 1 * s z) :=
          measurable_const.mul hs
        have habove : Measurable (fun z : (ℕ → ℝ) × ℝ => f 1 * z.1 1) :=
          measurable_const.mul hcoord_one
        exact Measurable.ite hcond hbelow habove
    | more n ih0 ih1 =>
        intro s hs
        simp only [revenue]
        have hcoord_next :
            Measurable (fun z : (ℕ → ℝ) × ℝ => z.1 (n + 2)) :=
          (measurable_pi_apply (n + 2)).comp measurable_fst
        have hthreshold :
            Measurable (fun z : (ℕ → ℝ) × ℝ => p (n + 1) + z.1 (n + 2)) :=
          measurable_const.add hcoord_next
        have hbelow_set :
            MeasurableSet {z : (ℕ → ℝ) × ℝ | s z < p (n + 1)} :=
          measurableSet_lt hs measurable_const
        have hmiddle_set :
            MeasurableSet
              {z : (ℕ → ℝ) × ℝ | s z < p (n + 1) + z.1 (n + 2)} :=
          measurableSet_lt hs hthreshold
        have hbelow :
            Measurable (fun z : (ℕ → ℝ) × ℝ =>
              revenue f p z.1 (n + 1) (s z)) := ih1 s hs
        have hmiddle_revenue :
            Measurable (fun z : (ℕ → ℝ) × ℝ =>
              revenue f p z.1 (n + 1) (p (n + 1))) :=
          ih1 (fun _ => p (n + 1)) measurable_const
        have hmiddle : Measurable (fun z : (ℕ → ℝ) × ℝ =>
            (s z - p (n + 1)) * f (n + 2) +
              revenue f p z.1 (n + 1) (p (n + 1))) := by
          exact ((hs.sub measurable_const).mul measurable_const).add hmiddle_revenue
        have hresidual :
            Measurable (fun z : (ℕ → ℝ) × ℝ => s z - z.1 (n + 2)) :=
          hs.sub hcoord_next
        have habove_revenue :
            Measurable (fun z : (ℕ → ℝ) × ℝ =>
              revenue f p z.1 (n + 1) (s z - z.1 (n + 2))) :=
          ih1 (fun z => s z - z.1 (n + 2)) hresidual
        have habove : Measurable (fun z : (ℕ → ℝ) × ℝ =>
            z.1 (n + 2) * f (n + 2) +
              revenue f p z.1 (n + 1) (s z - z.1 (n + 2))) := by
          exact (hcoord_next.mul measurable_const).add habove_revenue
        have hright : Measurable (fun z : (ℕ → ℝ) × ℝ =>
            if s z < p (n + 1) + z.1 (n + 2) then
              (s z - p (n + 1)) * f (n + 2) +
                revenue f p z.1 (n + 1) (p (n + 1))
            else
              z.1 (n + 2) * f (n + 2) +
                revenue f p z.1 (n + 1) (s z - z.1 (n + 2))) := by
          exact Measurable.ite (p := fun z : (ℕ → ℝ) × ℝ =>
            s z < p (n + 1) + z.1 (n + 2)) hmiddle_set hmiddle habove
        exact Measurable.ite hbelow_set hbelow hright
  intro n
  exact hgeneral n (fun z => z.2) measurable_snd
