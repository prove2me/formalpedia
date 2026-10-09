-- Prove2me | solution 1 for eq30NextPayoff_right_deriv_below_protection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:08:45.077003+00:00
-- url     : https://prove2.me/submissions/ec20b30b-f81f-4ce1-8360-581ad62ec40b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
open scoped Topology in
theorem solution
    (g : ℝ → ℝ) (p x fare s d : ℝ) (hs : s < p)
    (hg : HasDerivWithinAt g d (Set.Ici s) s) :
    HasDerivWithinAt (fun t => eq30NextPayoff g p x fare t)
      d (Set.Ici s) s := by
  have hlocal : (fun t => eq30NextPayoff g p x fare t) =ᶠ[𝓝[Set.Ici s] s]
      g := by
    have hupper : ∀ᶠ t : ℝ in 𝓝 s, t < p := Iio_mem_nhds hs
    have hupperWithin : ∀ᶠ t : ℝ in 𝓝[Set.Ici s] s, t < p :=
      hupper.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hupperWithin] with t ht htp
    simp [eq30NextPayoff, htp]
  have hbase : eq30NextPayoff g p x fare s = g s := by
    simp [eq30NextPayoff, hs]
  exact hg.congr_of_eventuallyEq hlocal hbase
