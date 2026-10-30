-- Prove2me | Theorems.Thm_DerivativeChainContinuation_appell_no_return_disk_bound
-- name    : DerivativeChainContinuation.appell_no_return_disk_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:00:04.808387+00:00
-- url     : https://prove2.me/theorems/30ffc9fd-115c-4948-9493-fcc87f6ee526
-- title:
--   A sparse Appell tail has a containing-disk chain bound
-- statement:
--   Let $2\le q\le M$ and $h\in\mathbb N$. Let $c_0=1$ and let $c_j=0$ for $j\le M$ outside $\{0,q\}$. Let $u,a\in\mathbb C$ and $D\ge0$, with all roots of $A_{M+h,u}$ in $|z-a|\le D$. An actual derivative chain starting at $u$ can be chosen with
--
--   $$L(z)\le\sqrt{h+1}\sqrt{D^2-|u-a|^2},$$
--
--   and with factor $\sqrt h$ when $c_q=0$. For $c:\mathbb N\to\mathbb C$, write $A_m(X)=\sum_{j=0}^m\binom mj c_jX^{m-j}$ and $A_{m,u}(X)=A_m(X-u)$. This transports the sparse-prefix estimate to an arbitrary containing-disk center.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellNoReturnBound.lean#L8-L40

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
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate



end DerivativeChainContinuation

theorem DerivativeChainContinuation.appell_no_return_disk_bound (M h q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (c : ℕ → ℂ) (hc0 : c 0=1) (hpref : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (u a : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ z : ℂ, (translatedAppell (M+h) c u).eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin (M+h) → ℂ,
      (∀ i, (derivative^[M+h-(i.val+1)] (translatedAppell (M+h) c u)).eval (z i)=0) ∧
      z ⟨0,by omega⟩=u ∧
      chainCost z ≤ Real.sqrt (h+1 : ℕ)*Real.sqrt (D^2-‖u-a‖^2) ∧
      (c q=0 → chainCost z ≤ Real.sqrt h*Real.sqrt (D^2-‖u-a‖^2)) := by sorry
