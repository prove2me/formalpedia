-- Prove2me | Theorems.Thm_AaronsonAmbainis_abstract_cs
-- name    : AaronsonAmbainis.abstract_cs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:21.360079+00:00
-- url     : https://prove2.me/theorems/5dea73e4-599a-4ad5-8663-94c67e7c4196
-- title:
--   Aaronson Ambainis: abstract cs
-- statement:
--   The lemma that removes the weights (Lemma 5.3 of the paper): Steps 1–3 and the conclusion of
--   its proof. The reciprocals are `⁻¹`, with `0⁻¹ = 0` in Lean, and the sets `O` and `N` may be
--   empty; so the first assertion of Lemma 5.3, that the sums `∑ j, a x j` and `∑ j, b y j` are
--   positive, is not part of this statement.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L209-L219
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L209-L219

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.abstract_cs {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, (∑ j, a x j)⁻¹) * (∑ y ∈ N, (∑ j, b y j)⁻¹) ≤ C := by sorry
