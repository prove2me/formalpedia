-- Prove2me | Theorems.Thm_AaronsonAmbainis_weight_choice
-- name    : AaronsonAmbainis.weight_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:22.062179+00:00
-- url     : https://prove2.me/theorems/029d3214-a835-42f2-878d-8ce39f143e58
-- title:
--   Aaronson Ambainis: weight choice
-- statement:
--   The choice of the weights `w j = 1 / (√(X j * Y j) + ε)`, `ε → 0`
--   (Step 2 of the proof of Lemma 5.3 of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L93-L127
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L93-L127

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.weight_choice {ι : Type*} [Fintype ι] (X Y : ι → ℝ) (hX : ∀ j, 0 ≤ X j)
    (hY : ∀ j, 0 ≤ Y j) (C Q : ℝ) (hC : 0 ≤ C)
    (h : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      Q ≤ (∑ j, w j * X j * Y j) * (C * ∑ j, (w j)⁻¹)) :
    Q ≤ C * (∑ j, Real.sqrt (X j * Y j)) ^ 2 := by sorry
