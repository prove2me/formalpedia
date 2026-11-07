-- Prove2me | Theorems.Thm_AaronsonAmbainis_pair_cs
-- name    : AaronsonAmbainis.pair_cs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:13.362207+00:00
-- url     : https://prove2.me/theorems/f5b56f91-7653-42ac-9af6-25d340f86734
-- title:
--   Aaronson Ambainis: pair cs
-- statement:
--   Cauchy–Schwarz over pairs.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L55-L74
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L55-L74

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.pair_cs {α β : Type*} (O : Finset α) (N : Finset β) (c s : α → β → ℝ)
    (hs : ∀ x ∈ O, ∀ y ∈ N, 0 < s x y) :
    (∑ x ∈ O, ∑ y ∈ N, c x y) ^ 2
      ≤ (∑ x ∈ O, ∑ y ∈ N, c x y ^ 2 * s x y) * (∑ x ∈ O, ∑ y ∈ N, (s x y)⁻¹) := by sorry
