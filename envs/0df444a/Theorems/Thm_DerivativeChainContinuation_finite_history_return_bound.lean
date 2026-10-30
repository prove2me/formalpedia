-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_history_return_bound
-- name    : DerivativeChainContinuation.finite_history_return_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:18:01.651731+00:00
-- url     : https://prove2.me/theorems/c370ad84-2b5a-411b-a431-200f42ce8c3d
-- title:
--   A centered finite history law yields a path with bounded total return cost
-- statement:
--   Let $I$ be finite, with nonnegative weights $w_i$ summing to one, and let $z_i:\mathbb N\to\mathbb C$ be paths. Let $h,d\in\mathbb N$, $\rho,D\ge0$, and $u,a\in\mathbb C$. Suppose their final mean is $u$, their endpoints lie in $|z-a|\le D$, and
--
--   $$\sum_iw_iE_h(z_i)=\sum_iw_i|z_i(h)-u|^2-\rho^2,$$
--
--   where $E_h(z)=\sum_{k<h}|z(k+1)-z(k)|^2$. If $d=h+1$ or $d=h$ with $\rho=0$, some history satisfies
--
--   $$\rho+\sum_{k<h}|z_i(k+1)-z_i(k)|+|z_i(h)-u|\le(1+\sqrt d)\sqrt{D^2-|u-a|^2}.$$
--
--   The expression includes the prefix radius, the tail and the closing edge.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/HistoryReturnEstimate.lean#L8-L47

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
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

theorem DerivativeChainContinuation.finite_history_return_bound {ι : Type} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℕ → ℂ) (h d : ℕ) (ρ D : ℝ) (u a : ℂ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) (hρ : 0 ≤ ρ) (hD : 0 ≤ D)
    (hd : d=h+1 ∨ (d=h ∧ ρ=0))
    (hm : ∑ i, (w i:ℂ)*z i h=u)
    (hb : ∀ i, ‖z i h-a‖ ≤ D)
    (he : (∑ i, w i*historyEnergy h (z i))=(∑ i, w i*‖z i h-u‖^2)-ρ^2) :
    ∃ i, ρ+(∑ k ∈ Finset.range h, ‖z i (k+1)-z i k‖)+‖z i h-u‖ ≤
      (1+Real.sqrt d)*Real.sqrt (D^2-‖u-a‖^2) := by sorry
