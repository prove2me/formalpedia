-- Prove2me | solution 1 for syracuse_descent_fifteen_mod_sixteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:15:20.664781+00:00
-- url     : https://prove2.me/submissions/e01681b1-a73d-4d87-9a5f-52428e0cef88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descent_progressions_fifteen_mod16
import Theorems.Thm_syracuse_descent_residual_fifteen_mod16_mod4096

theorem solution (n : ℕ) (h : n % 16 = 15) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hc : n % 128 = 15 ∨ n % 256 = 79 ∨ n % 256 = 95 ∨ n % 256 = 175 ∨ n % 1024 = 287 ∨ n % 1024 = 367 ∨ n % 1024 = 575 ∨ n % 1024 = 735 ∨ n % 1024 = 815 ∨ n % 1024 = 975 ∨ n % 4096 = 383 ∨ n % 4096 = 463 ∨ n % 4096 = 879 ∨ n % 4096 = 1087 ∨ n % 4096 = 1231 ∨ n % 4096 = 1647 ∨ n % 4096 = 1823 ∨ n % 4096 = 1855 ∨ n % 4096 = 2031 ∨ n % 4096 = 2239 ∨ n % 4096 = 2351 ∨ n % 4096 = 2591 ∨ n % 4096 = 2975 ∨ n % 4096 = 3119 ∨ n % 4096 = 3295 ∨ n % 4096 = 4063
  · obtain ⟨t, _, ht⟩ := syracuse_descent_progressions_fifteen_mod16 n hc
    exact ⟨t, ht⟩
  · push Not at hc
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25⟩ := hc
    exact syracuse_descent_residual_fifteen_mod16_mod4096 n h c0 ⟨c1, c2, c3⟩ ⟨c4, c5, c6, c7, c8, c9⟩ ⟨c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25⟩
