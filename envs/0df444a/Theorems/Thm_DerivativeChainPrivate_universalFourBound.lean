-- Prove2me | Theorems.Thm_DerivativeChainPrivate_universalFourBound
-- name    : DerivativeChainPrivate.universalFourBound
-- status  : Open
-- author  : @labuka
-- created : 2026-10-20T03:54:53.615602+00:00
-- url     : https://prove2.me/theorems/b82b1dcf-9882-48e5-acab-f0c98ada09e7
-- title:
--   Q2: universal derivative-chain four-bound
-- statement:
--   OPEN TARGET (non-strict four-bound). For every positive integer $n$ and every list $a_1,\ldots,a_n$ of complex numbers in the closed unit disk, let $p(X)=\prod_{j=1}^n(X-a_j)$. The target asserts that one can choose $z_m$ with $p^{(n-m)}(z_m)=0$ for every $1\le m\le n$ such that
--
--   $$\sum_{m=1}^{n-1}|z_{m+1}-z_m|\le4.$$
--
--   Repeated source roots are counted with multiplicity. There is no real-coefficient or nonreal-root-count restriction. No proof is claimed.
--
--   **Source convention.** Althöfer's [original announcement](https://althofer.de/prize-money-2.jpg) asks for total path length at most $C$ and suggests $C=4$. The target $L\le4$ stated here follows that convention.
-- source:
--   Ingo Althöfer, 15 August 2026 announcement, open question and prize (i)/(ii), path length at most C and suggested C=4: https://althofer.de/prize-money-2.jpg . Formal statement: Derivative-zero chains: public formalization reference, R07, DerivativeChainPrivate.universalFourBound. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
open scoped BigOperators
set_option autoImplicit false
open DerivativeChainPrivate

theorem DerivativeChainPrivate.universalFourBound {n : ℕ} (a : Fin n → ℂ)
    (hn : 1 ≤ n) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 4 := by sorry
