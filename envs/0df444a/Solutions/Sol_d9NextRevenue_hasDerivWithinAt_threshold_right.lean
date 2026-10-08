-- Prove2me | solution 1 for d9NextRevenue_hasDerivWithinAt_threshold_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:57:58.39348+00:00
-- url     : https://prove2.me/submissions/96ba6cd6-fc98-49f0-bba9-41904f1edc62

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
    (hG : HasDerivWithinAt g r (Set.Ici p) p)
    (hps : p < s) (hsx : s ≤ p + x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s) (r - fare)
      (Set.Ici p) p := by
  have hid : HasDerivWithinAt (fun u : ℝ => u) 1 (Set.Ici p) p :=
    hasDerivWithinAt_id p (Set.Ici p)
  have hseat := HasDerivWithinAt.const_mul fare
    (HasDerivWithinAt.const_sub s hid)
  have hlinear : HasDerivWithinAt
      (fun u : ℝ => (s - u) * fare + g u) (r - fare) (Set.Ici p) p := by
    have hsum := hseat.add hG
    have hfun : (fun u : ℝ => (s - u) * fare + g u) =
        (fun u => fare * (s - u) + g u) := by
      funext u
      ring
    have hder : r - fare = fare * (-1) + r := by ring
    rw [hfun, hder]
    exact hsum
  have hbranch : (fun u : ℝ => d9NextRevenue g u x fare s) =ᶠ[
      𝓝[Set.Ici p] p] (fun u => (s - u) * fare + g u) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hps)] with u hu hlt
    have hup : p ≤ u := Set.mem_Ici.mp hu
    have hus : u < s := Set.mem_Iio.mp hlt
    have hfirst : ¬ s < u := not_lt.mpr (le_of_lt hus)
    by_cases hmiddle : s < u + x
    · simp [d9NextRevenue, hfirst, hmiddle]
    · have hupper : s ≤ u + x := le_trans hsx (by linarith)
      have heq : s = u + x := le_antisymm hupper (le_of_not_gt hmiddle)
      have haccepted : s - u = x := by linarith
      have hresidual : s - x = u := by linarith
      simp [d9NextRevenue, hfirst, hmiddle, haccepted, hresidual]
  have hbase : d9NextRevenue g p x fare s = (s - p) * fare + g p := by
    have hfirst : ¬ s < p := not_lt.mpr (le_of_lt hps)
    by_cases hmiddle : s < p + x
    · simp [d9NextRevenue, hfirst, hmiddle]
    · have heq : s = p + x := le_antisymm hsx (le_of_not_gt hmiddle)
      have haccepted : s - p = x := by linarith
      have hresidual : s - x = p := by linarith
      simp [d9NextRevenue, hfirst, hmiddle, haccepted, hresidual]
  exact hlinear.congr_of_eventuallyEq hbranch hbase
