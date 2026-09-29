-- Prove2me | solution 1 for syracuse_descent_residual_twentyseven_mod32_mod8192
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T19:42:53.04376+00:00
-- url     : https://prove2.me/submissions/cdf7f719-eb8b-46a2-9df3-f2c9f701216a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descent_eight_more_progressions_twentyseven_mod32_mod8192
import Theorems.Thm_syracuse_descent_residual_twentyseven_mod32_mod8192_excl8

theorem solution (n : ℕ)
    (h : n % 32 = 27)
    (h128 : n % 128 ≠ 59)
    (h256 : n % 256 ≠ 123 ∧ n % 256 ≠ 219)
    (h1024 : n % 1024 ≠ 347 ∧ n % 1024 ≠ 507 ∧ n % 1024 ≠ 923)
    (h4096 : n % 4096 ≠ 1019 ∧ n % 4096 ≠ 1435 ∧ n % 4096 ≠ 1787 ∧
      n % 4096 ≠ 2203 ∧ n % 4096 ≠ 2587 ∧ n % 4096 ≠ 2907 ∧
      n % 4096 ≠ 3675)
    (h8192 : n % 8192 ≠ 539 ∧ n % 8192 ≠ 1563 ∧ n % 8192 ≠ 2075 ∧
      n % 8192 ≠ 3483 ∧ n % 8192 ≠ 3835 ∧ n % 8192 ≠ 4507 ∧
      n % 8192 ≠ 4859 ∧ n % 8192 ≠ 5371 ∧ n % 8192 ≠ 5723 ∧
      n % 8192 ≠ 6747 ∧ n % 8192 ≠ 7259) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hc : (n % 8192 = 2331 ∨ n % 8192 = 3067 ∨ n % 8192 = 4091 ∨
    n % 8192 = 4251 ∨ n % 8192 = 4955 ∨ n % 8192 = 5275 ∨
    n % 8192 = 5787 ∨ n % 8192 = 5979)
  · obtain ⟨t, _, hlt⟩ :=
      syracuse_descent_eight_more_progressions_twentyseven_mod32_mod8192 n hc
    exact ⟨t, hlt⟩
  · simp only [not_or] at hc
    exact syracuse_descent_residual_twentyseven_mod32_mod8192_excl8 n h h128 h256
      h1024 h4096 h8192 hc
