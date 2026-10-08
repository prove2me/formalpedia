-- Prove2me | solution 1 for revenue_integrable_of_seat_model
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:00:56.303008+00:00
-- url     : https://prove2.me/submissions/57d156e2-7469-4c26-a29a-bbff237a33d4

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => revenue f p (fun i => X i ω) (k + 1) s) P := by
  let S : Finset ℕ := Finset.Icc 1 (k + 1)
  let Mfare : ℝ := ∑ j ∈ S, |f j|
  have hMfare : 0 ≤ Mfare := by
    dsimp [Mfare]
    exact Finset.sum_nonneg fun j hj => abs_nonneg (f j)
  have hFare : ∀ j, 1 ≤ j → j ≤ k + 1 → |f j| ≤ Mfare := by
    intro j hj hjk
    have hjS : j ∈ S := by
      simp [S, Finset.mem_Icc, hj, hjk]
    change |f j| ≤ ∑ i ∈ S, |f i|
    exact Finset.single_le_sum (fun i hi => abs_nonneg (f i)) hjS
  have hseq : Measurable (fun ω : Ω => fun i : ℕ => X i ω) :=
    measurable_pi_lambda _ hM.meas
  have hRevenueMeas (s : ℝ) :
      Measurable (fun ω => revenue f p (fun i => X i ω) (k + 1) s) := by
    exact (revenue_joint_measurable f p (k + 1)).comp
      (Measurable.prodMk hseq measurable_const)
  letI : IsProbabilityMeasure P := hM.isProb
  have hC : 0 ≤ ((k + 1 : ℕ) : ℝ) * Mfare * s := by positivity
  have hbound : ∀ ω,
      ‖revenue f p (fun i => X i ω) (k + 1) s‖ ≤
        ‖((k + 1 : ℕ) : ℝ) * Mfare * s‖ := by
    intro ω
    have hb := revenue_abs_bound f p (fun i => X i ω) Mfare hMfare
      (fun j hj => hp j hj) (fun i => hM.nonneg i ω) (k + 1) s hs hFare
    calc
      ‖revenue f p (fun i => X i ω) (k + 1) s‖ =
          |revenue f p (fun i => X i ω) (k + 1) s| := Real.norm_eq_abs _
      _ ≤ ((k + 1 : ℕ) : ℝ) * Mfare * s := hb
      _ = ‖((k + 1 : ℕ) : ℝ) * Mfare * s‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hC]
  have hmajorant :
      Integrable (fun _ : Ω => ((k + 1 : ℕ) : ℝ) * Mfare * s) P :=
    integrable_const _
  refine hmajorant.mono' (hRevenueMeas s).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using hbound ω
