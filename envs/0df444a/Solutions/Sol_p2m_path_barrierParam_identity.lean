-- Prove2me | solution 1 for p2m_path_barrierParam_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:53:38.549946+00:00
-- url     : https://prove2.me/submissions/4f4141f0-0999-4c01-ae49-892551146ed8

import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
theorem solution {m n : ℕ} (δ : ℝ) (p : PDPoint m n) :
    ((n : ℝ) + m) * barrierParam δ p = δ * complementarity p := by
  unfold barrierParam
  by_cases hnm : n + m = 0
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst n
    subst m
    simp [complementarity, dotProduct]
  · have hpos : 0 < (n : ℝ) + m := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    field_simp [ne_of_gt hpos]
end
