-- Prove2me | Theorems.Thm_DerivativeChainPrivate_rb5_of_finite_prefix_budget
-- name    : DerivativeChainPrivate.rb5_of_finite_prefix_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:55:44.820984+00:00
-- url     : https://prove2.me/theorems/36d241d9-3ce4-4f61-a4ea-94c56e996ac7
-- title:
--   RB5 bound from explicit finite prefix and suffix budgets
-- statement:
--   Let $I$ be a finite index set. Let $w_i,T_i\in\mathbb R$, $Z_i\in\mathbb C$, and $a,S,L,N,c,u,V\in\mathbb R$. Assume $w_i\ge0$ and $\sum_{i\in I}w_i=1$. Assume also
--
--   $$0\le c<N,\qquad V\ge0,\qquad u^2+V\le1,$$
--
--   and, for every $i\in I$,
--
--   $$L\le T_i+|a-Z_i|+S,\qquad S\le1-|a|.$$
--
--   Suppose the two weighted bounds are
--
--   $$\sum_{i\in I}w_iT_i\le c\sqrt{V/N},\qquad
--   \sum_{i\in I}w_i|Z_i|\le\sqrt{u^2+cV/N}.$$
--
--   Then
--
--   $$L\le1+\sqrt{1+\frac{c^2}{N-c}}.$$
--
--   The real anchor $a$ is viewed as a complex number in the connector distance. No nonnegativity assumption on $T_i$, $S$, or $L$ is imposed. Weight normalization excludes an empty index set. This is a conditional finite-distribution bound; it does not construct the endpoints or establish these budgets for polynomial derivative chains.
-- source:
--   Derivative-zero chains: public formalization reference, R34, DerivativeChainPrivate.rb5_of_finite_prefix_budget. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Theorems.Thm_DerivativeChainPrivate_rb5_scalar
import Mathlib.Analysis.Complex.Norm

set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.rb5_of_finite_prefix_budget {ι : Type*} [Fintype ι]
    (w T : ι → ℝ) (Z : ι → ℂ) (a S L N c u V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hpath : ∀ i, L ≤ T i + ‖(a : ℂ) - Z i‖ + S)
    (hsuffix : S ≤ 1 - |a|)
    (hprefix : (∑ i, w i * T i) ≤ c * Real.sqrt (V / N))
    (hendpoint : (∑ i, w i * ‖Z i‖) ≤ Real.sqrt (u ^ 2 + c * V / N))
    (hc : 0 ≤ c) (hNc : c < N) (hV : 0 ≤ V) (huV : u ^ 2 + V ≤ 1) :
    L ≤ 1 + Real.sqrt (1 + c ^ 2 / (N - c)) := by sorry
