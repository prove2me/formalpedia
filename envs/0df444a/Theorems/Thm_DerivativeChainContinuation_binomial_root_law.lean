-- Prove2me | Theorems.Thm_DerivativeChainContinuation_binomial_root_law
-- name    : DerivativeChainContinuation.binomial_root_law
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:54:17.227215+00:00
-- url     : https://prove2.me/theorems/c992f4ba-ceca-42cf-b30d-a103999a3944
-- title:
--   Binomial roots carry a centered probability law on one circle
-- statement:
--   Let $q\ge2$ be a natural number and $c\in\mathbb C$. For $F(X)=X^q+c$, there are nonnegative weights $\pi_w$ on its distinct actual roots with
--
--   $$\sum_w\pi_w=1,\quad\sum_w\pi_ww=0,\quad w^q=-c,\quad |w|=|c|^{1/q}.$$
--
--   The last two conclusions hold for every root. The case $c=0$ is included. This provides the initial centered law for the finite-history construction.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/BinomialRootLaw.lean#L7-L30

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
open Polynomial
open scoped BigOperators



end DerivativeChainContinuation

theorem DerivativeChainContinuation.binomial_root_law (q : ℕ) (hq : 2 ≤ q) (c : ℂ) :
    let F : Polynomial ℂ := X^q+C c;
    ∃ π : F.roots.toFinset → ℝ,
      (∀ i, 0 ≤ π i) ∧ (∑ i, π i=1) ∧ (∑ i, (π i:ℂ)*(i:ℂ)=0) ∧
      (∀ i : F.roots.toFinset, (i:ℂ)^q= -c) ∧
      (∀ i : F.roots.toFinset, ‖(i:ℂ)‖=‖c‖^((q:ℝ)⁻¹)) := by sorry
