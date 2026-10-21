-- Prove2me | Theorems.Thm_DerivativeChainPrivate_universalConstantBound
-- name    : DerivativeChainPrivate.universalConstantBound
-- status  : Open
-- author  : @labuka
-- created : 2026-10-20T03:55:17.34459+00:00
-- url     : https://prove2.me/theorems/bc79e5a3-762f-4dc9-9e67-d1b047b03807
-- title:
--   Q1: degree-independent derivative-chain bound
-- statement:
--   OPEN TARGET. For every positive integer $n$ and every complex root list $a_1,\ldots,a_n$ in the closed unit disk, put $p(X)=\prod_{j=1}^n(X-a_j)$. A complete chain consists of points $z_m$ satisfying $p^{(n-m)}(z_m)=0$ for every $1\le m\le n$. The target is
--
--   $$\exists C\ge0\;\forall n\ge1\;\forall a_1,\ldots,a_n\in\overline{\mathbb D}\;\exists(z_1,\ldots,z_n),\qquad \sum_{m=1}^{n-1}|z_{m+1}-z_m|\le C.$$
--
--   The same constant must work for every degree and root list, with repeated roots counted with multiplicity. No proof is claimed.
--
--   **Source convention.** Althöfer's [original announcement](https://althofer.de/prize-money-2.jpg) asks for total path length at most $C$, with one constant independent of degree. The non-strict inequality $L\le C$ in this formal statement follows that convention. The separate four-bound target asks whether $C=4$ suffices.
-- source:
--   Ingo Althöfer, 15 August 2026 announcement, open question and prize (i)/(ii): https://althofer.de/prize-money-2.jpg . Exact formulation and strict/non-strict convention: Derivative-zero chains: public formalization reference, R08, DerivativeChainPrivate.universalConstantBound. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
open scoped BigOperators
set_option autoImplicit false
open DerivativeChainPrivate

theorem DerivativeChainPrivate.universalConstantBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a : Fin n → ℂ),
      1 ≤ n → (∀ i, ‖a i‖ ≤ 1) →
      ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ C := by sorry
