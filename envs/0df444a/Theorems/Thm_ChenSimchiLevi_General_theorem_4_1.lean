-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_theorem_4_1
-- name    : ChenSimchiLevi.General.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:12:00.500982+00:00
-- url     : https://prove2.me/theorems/b892ec00-bc4b-4844-9950-2e2b05224962
-- title:
--   Theorem 4.1(c)–(d): sym-$k$-concavity and optimal $(s,S,A,p)$ policy
-- statement:
--   In the finite-horizon general-demand model under Assumptions 1–5, for each $t=1,\ldots,T$ both the best-demand profit $G_t(y)=\max_d g_t(y,d)$ and the profit-to-go $v_t(x)$ are symmetrically $k$-concave.
--
--   There are $s_t\le S_t$, a possibly empty set $A_t\subseteq[s_t,(s_t+S_t)/2]$, and a maximizing expected-demand choice $d_t(y)$ at every post-order inventory $y$. The policy orders up to $S_t$ and selects $d_t(S_t)$ when $x<s_t$ or $x\in A_t$; otherwise it places no order and selects $d_t(x)$. In either case the chosen post-order level is feasible and attains the Bellman optimum:
--   $$v_t(x)=c_tx+\max_{y\ge x}\{-k\mathbf1_{\{y>x\}}+G_t(y)\}.$$
--   This gives the policy structure for general random demand, where ordinary $(s,S,p)$ policies can fail.
--
--   **Formalization Note** The policy's order region includes only the named set $A_t$ inside the stated closed interval; ties may be resolved either way. The assumptions explicitly include $c_{T+1}=0$, $c_t\ge0$, and $k\ge0$. The maximizing demand choice is a single function of the post-order level, so all states that order to $S_t$ use the same demand level and price.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 891, Theorem 4.1(c)–(d); proof p. 892

import Definitions.Def_ChenSimchiLevi_General_Model
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

namespace ChenSimchiLevi.General

/-- Theorem 4.1(c)–(d), p. 891. -/
theorem theorem_4_1 (M : Model) (hA : M.Assumptions) :
    ∀ t ∈ Finset.Icc 1 M.T,
      (SymKConvex M.k (fun y => -M.Gstar t y) ∧
       SymKConvex M.k (fun x => -M.v t x)) ∧
      ∃ (s S : ℝ) (A : Set ℝ) (dsel : ℝ → ℝ),
        s ≤ S ∧ A ⊆ Set.Icc s ((s + S) / 2) ∧
        (∀ y : ℝ, dsel y ∈ Set.Icc (M.dlo t) (M.dhi t) ∧
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) (dsel y)) ∧
        ∀ x : ℝ,
          x ≤ sSAOrder s S A x ∧
          (∀ y, x ≤ y →
            M.orderObj t x y ≤ M.orderObj t x (sSAOrder s S A x)) ∧
          M.v t x = M.c t * x + M.orderObj t x (sSAOrder s S A x) := by sorry

end ChenSimchiLevi.General
