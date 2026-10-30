-- Prove2me | Theorems.Thm_DerivativeChainContinuation_appell_centroid_return_bound
-- name    : DerivativeChainContinuation.appell_centroid_return_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:33:50.027825+00:00
-- url     : https://prove2.me/theorems/0f989487-e4d7-40ca-a6e8-e4ab5bb297c8
-- title:
--   A sparse Appell block admits a complete centroid-return chain
-- statement:
--   Let $M,h,s,q\in\mathbb N$, with $2\le q\le M$ and $s>0$. Let $c_0=1$, let $c_j=0$ for $j\le M$ outside $\{0,q\}$, and let $c_j=0$ for $M+h<j\le M+h+s$. Let $u,a\in\mathbb C$ and $D\ge0$, with all roots of $A_{M+h+s,u}$ in $|z-a|\le D$. There is an actual derivative chain starting at $u$ and returning permanently to $u$ from index $M+h$, with
--
--   $$L(z)\le(1+\sqrt{h+1})\sqrt{D^2-|u-a|^2}.$$
--
--   If $c_q=0$, the factor improves to $1+\sqrt h$. For $c:\mathbb N\to\mathbb C$, write $A_m(X)=\sum_{j=0}^m\binom mj c_jX^{m-j}$ and $A_{m,u}(X)=A_m(X-u)$. For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellReturnBound.lean#L6-L31

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

theorem DerivativeChainContinuation.appell_centroid_return_bound (M h s q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (hs : 0 < s) (c : ℕ → ℂ) (hc0 : c 0=1)
    (hpref : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (hreturn : ∀ j, M+h < j → j ≤ M+h+s → c j=0)
    (u a : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ z : ℂ, (translatedAppell (M+h+s) c u).eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin (M+h+s) → ℂ,
      (∀ i, (derivative^[M+h+s-(i.val+1)] (translatedAppell (M+h+s) c u)).eval (z i)=0) ∧
      z ⟨0,by omega⟩=u ∧ (∀ i, M+h ≤ i.val → z i=u) ∧
      chainCost z ≤ (1+Real.sqrt (h+1 : ℕ))*Real.sqrt (D^2-‖u-a‖^2) ∧
      (c q=0 → chainCost z ≤ (1+Real.sqrt h)*Real.sqrt (D^2-‖u-a‖^2)) := by sorry
