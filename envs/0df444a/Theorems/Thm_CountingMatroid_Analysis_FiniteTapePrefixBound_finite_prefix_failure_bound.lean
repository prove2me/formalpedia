-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_finite_prefix_failure_bound
-- name    : CountingMatroid.Analysis.FiniteTapePrefixBound.finite_prefix_failure_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:28:02.884217+00:00
-- url     : https://prove2.me/theorems/f41518b1-41e6-429c-9a2f-2514e6330915
-- title:
--   Uniform suffix failure bounds transfer across prefix-free histories
-- statement:
--   Let $m\in\mathbb N$, let $P$ be a finite prefix-free family of Boolean lists of lengths at most $m$, let $E$ be an event on Boolean lists, and let $\beta\in[0,\infty]$. Assume every length-$m$ list satisfying $E$ has some prefix in $P$. Assume also that every $p\in P$ has conditional suffix failure bound
--
--   $$2^{-(m-|p|)}\bigl|\{s:|s|=m-|p|,\ E(p\mathbin{+\!+}s)\}\bigr|\le\beta.$$
--
--   Then
--
--   $$2^{-m}\bigl|\{b:|b|=m,\ E(b)\}\bigr|\le\beta.$$
--
--   Histories may have different lengths. The result is finite counting and needs no independence between separate algorithmic phase events.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteTapePrefixBound.lean#L155-L207

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

theorem CountingMatroid.Analysis.FiniteTapePrefixBound.finite_prefix_failure_bound (m : ℕ) (P : Finset (List Bool))
    (E : List Bool → Prop) (β : ENNReal)
    (hlen : ∀ pref ∈ P, pref.length ≤ m)
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b)
    (hcover : ∀ bits, bits.length = m → E bits →
      ∃ pref ∈ P, pref <+: bits)
    (hconditional : ∀ pref ∈ P,
      (Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length) ≤ β) :
    (Set.ncard {bits : List Bool | bits.length = m ∧ E bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ β := by sorry
