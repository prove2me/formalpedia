-- Prove2me | Theorems.Thm_Erdos195_twosComplement_no_exhaustive_safe_chain
-- name    : Erdos195.twosComplement_no_exhaustive_safe_chain
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-22T21:15:20.219984+00:00
-- url     : https://prove2.me/theorems/e3b99f5d-d4c7-4cf8-b80c-5d368d89930c
-- title:
--   No exhaustive chain of safe words for the two's-complement order
-- statement:
--   There is no sequence $P_0,P_1,P_2,\dots$ of finite lists of integers such that
--
--   1. each $P_n$ is safe for the two's-complement order $\prec_{\mathrm{true}}$,
--   2. each $P_n$ is a prefix of $P_{n+1}$, and
--   3. every integer occurs in some $P_n$.
--
--   So Ho's construction cannot be carried out on $\mathbb{Z}$ with the fixed completion order $\prec_{\mathrm{true}}$. A construction for the goal must change the completion order between stages or use different ideas.
--
--   **Formalization Note** `compLt R P x y` holds when both lie in `P` with `x` at a smaller index, or `x ∈ P` and `y ∉ P`, or neither lies in `P` and `R x y`. `Safe R P` says there are no `a` and `r ≠ 0` with `compLt R P a (a+r)`, `compLt R P (a+r) (a+2r)` and `compLt R P (a+2r) (a+3r)`. `epsLt ε x y` is `x ≠ y ∧ (x / 2^k % 2 = 1 ↔ ε k = true)` with `k = padicValInt 2 (y - x)`, i.e. $k=\nu_2(y-x)$; integer division is floor division, so `x / 2^k % 2` is the $k$-th two's-complement digit of $x$.
-- source:
--   New to this mission (obstruction to transferring B. S. Ho, arXiv:2609.12780, proof of the Theorem, to ℤ)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem twosComplement_no_exhaustive_safe_chain (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt (fun _ => true)) (P n))
    (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x, ∃ n, x ∈ P n) : False := by sorry

end Erdos195
