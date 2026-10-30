-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sparse_appell_chain_bound
-- name    : DerivativeChainContinuation.sparse_appell_chain_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:57:50.157915+00:00
-- url     : https://prove2.me/theorems/8e3caf97-3014-45e0-be6f-bda575712465
-- title:
--   A sparse Appell prefix and arbitrary tail give a square-root chain bound
-- statement:
--   Let $M,h,q\in\mathbb N$ with $2\le q\le M$, let $c_0=1$, and suppose $c_j=0$ for $j\le M$ outside $\{0,q\}$. Let $u\in\mathbb C$ and $R\ge0$. If every root of $A_{M+h,u}$ has modulus at most $R$, there is an actual derivative chain starting at $u$ with
--
--   $$L(z)\le\sqrt{h+1}\sqrt{R^2-|u|^2},\qquad c_q=0\Longrightarrow L(z)\le\sqrt h\sqrt{R^2-|u|^2}.$$
--
--   For $c:\mathbb N\to\mathbb C$, write $A_m(X)=\sum_{j=0}^m\binom mj c_jX^{m-j}$ and $A_{m,u}(X)=A_m(X-u)$. For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$. Coefficients after the sparse prefix are unrestricted.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SparseAppellChain.lean#L13-L92

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
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators




end DerivativeChainContinuation

theorem DerivativeChainContinuation.sparse_appell_chain_bound (M h q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (c : ℕ → ℂ) (hc0 : c 0=1)
    (hs : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (u : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z : ℂ, (translatedAppell (M+h) c u).eval z=0 → ‖z‖ ≤ R) :
    ∃ z : Fin (M+h) → ℂ,
      (∀ i, (derivative^[M+h-(i.val+1)] (translatedAppell (M+h) c u)).eval (z i)=0) ∧
      z ⟨0,by omega⟩=u ∧ chainCost z ≤ Real.sqrt (h+1)*Real.sqrt (R^2-‖u‖^2) ∧
      (c q=0 → chainCost z ≤ Real.sqrt h*Real.sqrt (R^2-‖u‖^2)) := by sorry
