-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricGraphLine_odd_no_three_actual_centers
-- name    : CompactnessConjecture.symmetricGraphLine_odd_no_three_actual_centers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/69973489-fe03-416e-bf4f-cbe492b79621
-- title:
--   CompactnessConjecture.symmetricGraphLine_odd_no_three_actual_centers
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symmetricGraphLine_odd_no_three_actual_centers
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hcenter₀ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₀ y₀
            (projectiveDirection_nonzero_left K h01)).1)
    (hcenter₁ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₁ y₁
            (projectiveDirection_nonzero_right K h01)).1)
    (hcenter₂ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₂ y₂
            (projectiveDirection_nonzero_right K h02)).1) :
    False := by sorry
