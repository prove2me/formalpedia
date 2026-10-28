-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_stopping_prefixes_free
-- name    : CountingMatroid.Analysis.FiniteTapePrefixBound.stopping_prefixes_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:26:12.229986+00:00
-- url     : https://prove2.me/theorems/9dd24e8b-f1fc-409a-8328-13d9876760ea
-- title:
--   Replay-stable stopping histories form a prefix-free family
-- statement:
--   Let $m\in\mathbb N$, let $S$ be a finite family of Boolean lists all of length $m$, and let $c$ assign a natural cursor to every Boolean list. Assume that for all $a,b\in S$,
--
--   $$c(a)\le m\ \text{ and }\ \operatorname{take}_{c(a)}(a)\preceq b\quad\Longrightarrow\quad c(b)=c(a).$$
--
--   Let $P=\{\operatorname{take}_{c(a)}(a):a\in S\}$. Then
--
--   $$u,v\in P,\quad u\preceq v\quad\Longrightarrow\quad u=v.$$
--
--   No global cursor-coverage assumption is imposed. A cursor beyond the list length contributes the entire list as its taken prefix.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteTapePrefixBound.lean#L70-L90

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

theorem CountingMatroid.Analysis.FiniteTapePrefixBound.stopping_prefixes_free (m : ℕ) (S : Finset (List Bool))
    (cursor : List Bool → ℕ) (hlen : ∀ bits ∈ S, bits.length = m)
    (hreplay : ∀ bitsA ∈ S, ∀ bitsB ∈ S, cursor bitsA ≤ m →
      bitsA.take (cursor bitsA) <+: bitsB → cursor bitsB = cursor bitsA) :
    ∀ a ∈ S.image (fun bits => bits.take (cursor bits)),
      ∀ b ∈ S.image (fun bits => bits.take (cursor bits)), a <+: b → a = b := by sorry
