-- Prove2me | solution 1 for eq30_hasDerivWithinAt_of_right_affine
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:28:36.43778+00:00
-- url     : https://prove2.me/submissions/44cf0cbd-535a-4d7a-b9bc-081108234323

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false
open Filter Topology

theorem solution
    (g : ℝ → ℝ) (s d δ : ℝ) (hδ : 0 < δ)
    (haff : ∀ t, t ∈ Set.Ici s → t < s + δ →
      g t = g s + d * (t - s)) :
    HasDerivWithinAt g d (Set.Ici s) s := by
  have hf : HasDerivAt (fun t : ℝ => g s + d * (t - s)) d s := by
    have := ((hasDerivAt_id s).sub_const s).const_mul d |>.const_add (g s)
    simpa using this
  have hev : ∀ᶠ t in 𝓝[Set.Ici s] s, g t = g s + d * (t - s) := by
    have h1 : ∀ᶠ t in 𝓝[Set.Ici s] s, t < s + δ :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
    filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht2
    exact haff t ht2 ht1
  exact hf.hasDerivWithinAt.congr_of_eventuallyEq hev (by simp)
