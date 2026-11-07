-- Prove2me | Theorems.Thm_AaronsonAmbainis_cs_core
-- name    : AaronsonAmbainis.cs_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:19.714603+00:00
-- url     : https://prove2.me/theorems/6070fad2-b382-46f1-b5af-123faf642453
-- title:
--   Aaronson Ambainis: cs core
-- statement:
--   The Cauchy–Schwarz argument with general coefficients `u`, `v` satisfying
--   `u x ^ 2 * ∑ j, a x j = u x` and `v y ^ 2 * ∑ j, b y j = v y`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L138-L203
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L138-L203

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.cs_core {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (u : α → ℝ) (v : β → ℝ)
    (hua : ∀ x, u x ^ 2 * ∑ j, a x j = u x) (hvb : ∀ y, v y ^ 2 * ∑ j, b y j = v y)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, u x) * (∑ y ∈ N, v y) ≤ C := by sorry
