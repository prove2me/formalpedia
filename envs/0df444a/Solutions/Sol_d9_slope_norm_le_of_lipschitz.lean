-- Prove2me | solution 1 for d9_slope_norm_le_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:38:19.728161+00:00
-- url     : https://prove2.me/submissions/69129173-f92a-4c55-be97-933585088713

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (g : ℝ → ℝ) (K a b : ℝ) (hK : 0 ≤ K)
    (hLip : |g b - g a| ≤ K * |b - a|) :
    ‖slope g a b‖ ≤ K := by
  by_cases hab : a = b
  · subst b
    simp [hK]
  · have hden : 0 < |b - a| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hab))
    have hquot : |g b - g a| / |b - a| ≤ K := by
      apply (div_le_iff₀ hden).2
      nlinarith
    rw [slope_def_field, Real.norm_eq_abs, abs_div]
    simpa [abs_of_pos hden] using hquot
