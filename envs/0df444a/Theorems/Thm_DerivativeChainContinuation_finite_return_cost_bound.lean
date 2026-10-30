-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_return_cost_bound
-- name    : DerivativeChainContinuation.finite_return_cost_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:16:17.170905+00:00
-- url     : https://prove2.me/theorems/c3980599-d0ad-449e-97ee-a314904ace3b
-- title:
--   A finite weighted square budget selects a bounded return cost
-- statement:
--   Let $I$ be a finite type, let $w_i\ge0$ sum to one, and let $f_i,g_i\ge0$. For $d\in\mathbb N$ and $V\in\mathbb R$, suppose
--
--   $$\sum_iw_if_i^2\le d\sum_iw_ig_i^2,\qquad \sum_iw_ig_i^2\le V.$$
--
--   Then some $i\in I$ satisfies
--
--   $$f_i+g_i\le(1+\sqrt d)\sqrt V.$$
--
--   This is the finite selection step that pays for a path and its return edge.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteReturnBound.lean#L6-L30

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



end DerivativeChainContinuation

theorem DerivativeChainContinuation.finite_return_cost_bound {ι : Type} [Fintype ι]
    (w f g : ι → ℝ) (d : ℕ) (V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfg : (∑ i, w i*(f i)^2) ≤ (d:ℝ)*(∑ i, w i*(g i)^2))
    (hV : (∑ i, w i*(g i)^2) ≤ V) :
    ∃ i, f i+g i ≤ (1+Real.sqrt d)*Real.sqrt V := by sorry
