-- Prove2me | Theorems.Thm_DerivativeChainContinuation_appell_centroid_return_parameter
-- name    : DerivativeChainContinuation.appell_centroid_return_parameter
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:31:42.775488+00:00
-- url     : https://prove2.me/theorems/98f44524-ea44-48cf-b1d6-5fc5bd5822fb
-- title:
--   A sparse Appell block returns to the centroid with a parameterized bound
-- statement:
--   Let $M,h,s,q,d\in\mathbb N$, with $2\le q\le M$ and $s>0$. Let $c_0=1$, let $c_j=0$ for $j\le M$ outside $\{0,q\}$, and let $c_j=0$ for $M+h<j\le M+h+s$. Let $u,a\in\mathbb C$ and $D\ge0$, with every root of $A_{M+h+s,u}$ in $|z-a|\le D$. If $d=h+1$ or $d=h$ with $c_q=0$, there is an actual derivative chain starting at $u$, equal to $u$ at every index $i\ge M+h$, and satisfying
--
--   $$L(z)\le(1+\sqrt d)\sqrt{D^2-|u-a|^2}.$$
--
--   For $c:\mathbb N\to\mathbb C$, write $A_m(X)=\sum_{j=0}^m\binom mj c_jX^{m-j}$ and $A_{m,u}(X)=A_m(X-u)$. The admissible parameter records the improved zero-mode case.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellCentroidReturn.lean#L13-L99

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
set_option maxHeartbeats 2000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



end DerivativeChainContinuation

theorem DerivativeChainContinuation.appell_centroid_return_parameter (M h s q d : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (hs : 0 < s) (c : ℕ → ℂ) (hc0 : c 0=1)
    (hpref : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (hreturn : ∀ j, M+h < j → j ≤ M+h+s → c j=0)
    (hd : d=h+1 ∨ (d=h ∧ c q=0))
    (u a : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ z : ℂ, (translatedAppell (M+h+s) c u).eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin (M+h+s) → ℂ,
      (∀ i, (derivative^[M+h+s-(i.val+1)] (translatedAppell (M+h+s) c u)).eval (z i)=0) ∧
      z ⟨0,by omega⟩=u ∧ (∀ i, M+h ≤ i.val → z i=u) ∧
      chainCost z ≤ (1+Real.sqrt d)*Real.sqrt (D^2-‖u-a‖^2) := by sorry
