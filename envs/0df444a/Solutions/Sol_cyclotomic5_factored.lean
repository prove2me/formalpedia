-- Prove2me | solution 1 for cyclotomic5_factored
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:06:20.830216+00:00
-- url     : https://prove2.me/submissions/209bbac6-9e99-43bb-a2cd-181daed4e144

import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) :
    (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = a ^ 5 + b ^ 5 := by ring
