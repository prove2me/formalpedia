-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_prefix_mass_le_one
-- name    : CountingMatroid.Analysis.FiniteTapePrefixBound.prefix_mass_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:25:43.535406+00:00
-- url     : https://prove2.me/theorems/50747b97-591c-45cb-afb8-7181c6de6f41
-- title:
--   Finite prefix-free histories have total fair-bit mass at most one
-- statement:
--   Let $m\in\mathbb N$ and let $P$ be a finite family of Boolean lists, each of length at most $m$. Assume $P$ is prefix-free: comparable members under the prefix relation are equal. Then
--
--   $$\sum_{p\in P}2^{-|p|}\le1.$$
--
--   The formal statement uses extended nonnegative reals. This finite Kraft inequality bounds the total probability of distinct consumed histories.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteTapePrefixBound.lean#L105-L153

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteTapePrefixBound

theorem CountingMatroid.Analysis.FiniteTapePrefixBound.prefix_mass_le_one (m : ℕ) (P : Finset (List Bool))
    (hlen : ∀ pref ∈ P, pref.length ≤ m)
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b) :
    ∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length ≤ 1 := by sorry
