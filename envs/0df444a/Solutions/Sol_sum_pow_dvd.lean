-- Prove2me | solution 1 for sum_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T05:41:09.142431+00:00
-- url     : https://prove2.me/submissions/1d2f26af-c21e-42e3-8b93-5ef5a6020e32

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : (a + b) ∣ a ^ 5 + b ^ 5 :=
  ⟨a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4, by ring⟩
