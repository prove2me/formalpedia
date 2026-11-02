-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile
-- name    : AvramDividend.Classical.avram_wave5_04c_tapered_compact_profile
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:20:48.298287+00:00
-- url     : https://prove2.me/theorems/8557bc41-4f59-4b20-89c6-46be6f6bf010
-- title:
--   Taper compactified C1 jump profile with zero far-tail and exact near-endpoint match
-- statement:
--   Given any continuous compactified jump profile on [a,1] and a<b≤1, construct an actual continuous unit-interval function equal to zero for t≤a and exactly equal to the original profile for t≥b. The linear taper in [a,b] and clamp to [a,1] avoid log singularity at t=0 and give an exact finite-band range for the C1 Levy semigroup approximation. This is the constructive compact cutoff bridging weighted Bernstein polynomials and source/Lévy jump tails.
-- source:
--   ContinuousOn.comp, continuous min/max, continuousOn_iff_continuous_restrict, elementary interval cut-off inequalities.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_tapered_compact_profile
    (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hb : b ≤ 1)
    (hf : ContinuousOn f (Set.Icc a 1)) :
    ∃ G : C(unitInterval.Elem, ℝ),
      (∀ t : unitInterval.Elem, (t : ℝ) ≤ a → G t = 0) ∧
      (∀ t : unitInterval.Elem, b ≤ (t : ℝ) → G t = f (t : ℝ)) := by sorry
