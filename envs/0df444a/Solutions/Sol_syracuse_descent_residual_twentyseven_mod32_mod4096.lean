-- Prove2me | solution 1 for syracuse_descent_residual_twentyseven_mod32_mod4096
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T02:03:16.783407+00:00
-- url     : https://prove2.me/submissions/15ec8ff4-163c-4d8d-afa3-d90e067603ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descent_progressions_twentyseven_mod32_mod8192
import Theorems.Thm_syracuse_descent_residual_twentyseven_mod32_mod8192

/-!
# Existing 4096 residual branch via an 8192 split

This module proves the existing residual statement by splitting its input
among the eleven new modulo-8192 progression classes and their complement.
-/

/-- The existing twenty-seven modulo thirty-two residual statement. -/
theorem solution (n : ℕ)
    (h : n % 32 = 27)
    (h128 : n % 128 ≠ 59)
    (h256 : n % 256 ≠ 123 ∧ n % 256 ≠ 219)
    (h1024 : n % 1024 ≠ 347 ∧ n % 1024 ≠ 507 ∧ n % 1024 ≠ 923)
    (h4096 : n % 4096 ≠ 1019 ∧ n % 4096 ≠ 1435 ∧ n % 4096 ≠ 1787 ∧
      n % 4096 ≠ 2203 ∧ n % 4096 ≠ 2587 ∧ n % 4096 ≠ 2907 ∧
      n % 4096 ≠ 3675) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hres : n % 8192 = 539 ∨ n % 8192 = 1563 ∨ n % 8192 = 2075 ∨
      n % 8192 = 3483 ∨ n % 8192 = 3835 ∨ n % 8192 = 4507 ∨
      n % 8192 = 4859 ∨ n % 8192 = 5371 ∨ n % 8192 = 5723 ∨
      n % 8192 = 6747 ∨ n % 8192 = 7259
  · obtain ⟨t, ht, hdesc⟩ :=
      syracuse_descent_progressions_twentyseven_mod32_mod8192 n hres
    exact ⟨t, hdesc⟩
  · apply syracuse_descent_residual_twentyseven_mod32_mod8192 n h h128 h256 h1024 h4096
    simpa only [not_or] using hres
