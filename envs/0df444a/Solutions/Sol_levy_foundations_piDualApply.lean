-- Prove2me | solution 1 for levy_foundations_piDualApply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:08:12.173202+00:00
-- url     : https://prove2.me/submissions/f08e0cff-0397-42be-9592-2f44f2610934

import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Probability.Independence.CharacteristicFunction


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by
  have realDualApply (M : StrongDual ℝ ℝ) (r : ℝ) :
      M r = r * M 1 := by
    conv_rhs => rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realDualApply (L.comp
    (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) (x i)]
  rfl
