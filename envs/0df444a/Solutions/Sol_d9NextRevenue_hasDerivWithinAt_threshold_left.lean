-- Prove2me | solution 1 for d9NextRevenue_hasDerivWithinAt_threshold_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:58:44.161212+00:00
-- url     : https://prove2.me/submissions/4fceb05a-8e64-4158-87ab-a9a2d9bc4060

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
open scoped Topology
theorem solution
    (g : ℝ → ℝ) (p x fare s r : ℝ)
    (hG : HasDerivWithinAt g r (Set.Iic p) p)
    (hps : p ≤ s) (hsx : s < p + x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s) (r - fare)
      (Set.Iic p) p := by
  have hid : HasDerivWithinAt (fun u : ℝ => u) 1 (Set.Iic p) p :=
    hasDerivWithinAt_id p (Set.Iic p)
  have hseat := HasDerivWithinAt.const_mul fare
    (HasDerivWithinAt.const_sub s hid)
  have hlinear : HasDerivWithinAt
      (fun u : ℝ => (s - u) * fare + g u) (r - fare) (Set.Iic p) p := by
    have hsum := hseat.add hG
    have hfun : (fun u : ℝ => (s - u) * fare + g u) =
        (fun u => fare * (s - u) + g u) := by
      funext u
      ring
    have hder : r - fare = fare * (-1) + r := by ring
    rw [hfun, hder]
    exact hsum
  have hcut : s - x < p := by linarith
  have hbranch : (fun u : ℝ => d9NextRevenue g u x fare s) =ᶠ[
      𝓝[Set.Iic p] p] (fun u => (s - u) * fare + g u) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcut)] with u hu hnear
    have hup : u ≤ p := Set.mem_Iic.mp hu
    have hmid : s < u + x := by linarith [Set.mem_Ioi.mp hnear]
    have hfirst : ¬ s < u := not_lt.mpr (le_trans hup hps)
    simp [d9NextRevenue, hfirst, hmid]
  have hbase : d9NextRevenue g p x fare s = (s - p) * fare + g p := by
    have hfirst : ¬ s < p := not_lt.mpr hps
    simp [d9NextRevenue, hfirst, hsx]
  exact hlinear.congr_of_eventuallyEq hbranch hbase
