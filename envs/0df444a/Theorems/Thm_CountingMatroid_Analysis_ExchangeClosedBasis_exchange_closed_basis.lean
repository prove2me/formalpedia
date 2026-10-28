-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ExchangeClosedBasis_exchange_closed_basis
-- name    : CountingMatroid.Analysis.ExchangeClosedBasis.exchange_closed_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:51:37.217588+00:00
-- url     : https://prove2.me/theorems/54683b48-607a-4881-9ade-aeacc77cbc27
-- title:
--   Insertion failure and exchange closure certify a restricted basis
-- statement:
--   Let $M$ be a matroid on an arbitrary ambient type, let $I$ be an independent set, and let $X\subseteq M.E$. Suppose every $e\in X\setminus I$ fails to extend $I$ independently, and every successful single-element exchange with such an $e$ removes an element of $X$: $$e\in X\setminus I\ \Longrightarrow\ I\cup\{e\}\text{ is dependent},$$ $$e\in X\setminus I,\ u\in I,\ (I\setminus\{u\})\cup\{e\}\text{ independent}\ \Longrightarrow\ u\in X.$$ Then $$I\cap X\text{ is a basis of }X\text{ in }M.$$ No finiteness assumption is imposed. This gives a basis certificate from local insertion and exchange conditions.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangeClosedBasis.lean#L13-L40

import Definitions.Def_CountingMatroid_Model_Prelude
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Rat.Defs

namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
set_option autoImplicit false

/-!
A closure certificate for a part of an independent set. When no element of
that part's ambient set can be inserted, and every permitted exchange stays
in the ambient set, fundamental circuits prove that the part is a basis.
-/

namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeClosedBasis

theorem CountingMatroid.Analysis.ExchangeClosedBasis.exchange_closed_basis {α : Type*} (M : Matroid α) (I X : Set α)
    (hI : M.Indep I) (hX : X ⊆ M.E)
    (hinsert : ∀ e ∈ X, e ∉ I → ¬ M.Indep (insert e I))
    (hexchange : ∀ e ∈ X, e ∉ I → ∀ u ∈ I,
      M.Indep (insert e (I \ {u})) → u ∈ X) :
    M.IsBasis (I ∩ X) X := by sorry
