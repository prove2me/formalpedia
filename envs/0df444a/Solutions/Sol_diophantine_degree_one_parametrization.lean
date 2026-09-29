-- Prove2me | solution 1 for diophantine_degree_one_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T02:47:34.870381+00:00
-- url     : https://prove2.me/submissions/abbbc187-51ec-4e44-950d-aa60c743b1af

import Mathlib.Tactic

theorem solution (a b r s : Int)
    (hs : s = 1 ∨ s = -1) (hr : a * b + 1 = r ^ 2) :
    (r + s * a) ^ 2 = a * (a + b + 2 * s * r) + 1 ∧
    (b + s * r) ^ 2 = b * (a + b + 2 * s * r) + 1 ∧
    a + (a + b + 2 * s * r) + b + 2 * a * (a + b + 2 * s * r) * b
      + 2 * (r + s * a) * r * (b + s * r)
      = 4 * r * (r + s * a) * (b + s * r) := by
  rcases hs with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩ <;> try (linear_combination -hr)
    linear_combination 2 * (a + b + r) * hr
  · refine ⟨?_, ?_, ?_⟩ <;> try (linear_combination -hr)
    linear_combination 2 * (a + b - r) * hr
