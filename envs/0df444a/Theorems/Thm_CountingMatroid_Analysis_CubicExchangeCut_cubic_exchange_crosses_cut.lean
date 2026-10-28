-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CubicExchangeCut_cubic_exchange_crosses_cut
-- name    : CountingMatroid.Analysis.CubicExchangeCut.cubic_exchange_crosses_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:46:59.331861+00:00
-- url     : https://prove2.me/theorems/bfd60051-61b5-421e-84e3-a4cd015e19f0
-- title:
--   Cubic exchange support crosses every active cut
-- statement:
--   Let $\sigma$ have decidable equality, with no finiteness assumption. Let $T:\sigma^3\to\mathbb Q$ satisfy $T_{sij}=T_{isj}$ and $T_{sij}=T_{sji}$. Let
--   $$S=\{e_i+e_j+e_s:T_{sij}\ne0\}.$$
--   Write $e_i$ for a unit exponent vector. The exchange condition on a set $S$ of finitely supported natural exponent vectors is: for all $x,y\in S$ and $i$ with $y_i<x_i$, some $j$ satisfies $x_j<y_j$ and $x-e_i+e_j\in S$. Assume that $S$ satisfies it. For any $U\subseteq\sigma$, suppose some nonzero entry has first index in $U$ and another has first index outside $U$. Then
--
--   $$\exists s,i,j:\quad T_{sij}\ne0,\quad i\in U,\quad j\notin U.$$
--
--   Thus active tensor coordinates cannot separate into two uncoupled blocks. Entrywise nonnegativity is not required.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CubicExchangeCut.lean#L13-L91

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
set_option autoImplicit false

/-!
Exchange support prevents a cubic tensor from splitting into two nonzero
blocks with no entry joining them. This is the combinatorial input to the
spectral local-to-global argument; no spectral conclusion is asserted here.
-/

namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicExchangeCut

theorem CountingMatroid.Analysis.CubicExchangeCut.cubic_exchange_crosses_cut {σ : Type} [DecidableEq σ]
    (T : σ → σ → σ → ℚ)
    (hswap : ∀ s i j, T s i j = T i s j)
    (hlast : ∀ s i j, T s i j = T s j i)
    (S : Set (σ →₀ ℕ))
    (hsupport : ∀ x, x ∈ S ↔ ∃ s i j, T s i j ≠ 0 ∧
      x = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1)
    (hex : ∀ x ∈ S, ∀ y ∈ S, ∀ i, y i < x i →
      ∃ j, x j < y j ∧ x - Finsupp.single i 1 + Finsupp.single j 1 ∈ S)
    (U : Set σ)
    (hin : ∃ s i j, T s i j ≠ 0 ∧ s ∈ U)
    (hout : ∃ s i j, T s i j ≠ 0 ∧ s ∉ U) :
    ∃ s i j, T s i j ≠ 0 ∧ i ∈ U ∧ j ∉ U := by sorry
