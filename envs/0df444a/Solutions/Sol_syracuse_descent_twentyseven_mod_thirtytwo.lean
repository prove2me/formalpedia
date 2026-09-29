-- Prove2me | solution 1 for syracuse_descent_twentyseven_mod_thirtytwo
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:15:19.838236+00:00
-- url     : https://prove2.me/submissions/2fc7c57a-5ae7-4d54-99ae-689158a55c83
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descent_progressions_twentyseven_mod32
import Theorems.Thm_syracuse_descent_residual_twentyseven_mod32_mod4096

theorem solution (n : ℕ) (h : n % 32 = 27) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hc : n % 128 = 59 ∨ n % 256 = 123 ∨ n % 256 = 219 ∨ n % 1024 = 347 ∨ n % 1024 = 507 ∨ n % 1024 = 923 ∨ n % 4096 = 1019 ∨ n % 4096 = 1435 ∨ n % 4096 = 1787 ∨ n % 4096 = 2203 ∨ n % 4096 = 2587 ∨ n % 4096 = 2907 ∨ n % 4096 = 3675
  · obtain ⟨t, _, ht⟩ := syracuse_descent_progressions_twentyseven_mod32 n hc
    exact ⟨t, ht⟩
  · push Not at hc
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hc
    exact syracuse_descent_residual_twentyseven_mod32_mod4096 n h c0 ⟨c1, c2⟩ ⟨c3, c4, c5⟩ ⟨c6, c7, c8, c9, c10, c11, c12⟩
