-- Prove2me | Theorems.Thm_CaiCandesShen_GeneralConvex_subgradient_strongly_monotone
-- name    : CaiCandesShen.GeneralConvex.subgradient_strongly_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:19:40.990455+00:00
-- url     : https://prove2.me/theorems/47cb4d6f-c734-4a75-adb0-66faba707e8a
-- title:
--   Lemma 4.1 — subgradients of $f_\tau$ are strongly monotone
-- statement:
--   Let $\tau>0$ and $f_\tau(X) = \tau\|X\|_* + \tfrac12\|X\|_F^2$ on real $n_1\times n_2$ matrices. If $Z\in\partial f_\tau(X)$ and $Z'\in\partial f_\tau(X')$, then
--   $$\langle Z - Z', X - X'\rangle \ge \|X - X'\|_F^2 .$$
--
--   This expresses the strong convexity of $f_\tau$ with modulus one, and it is the inequality through which the convergence proofs of §4 turn a dual inequality into a bound on $\|X^k - X^\star\|_F$.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1968, Lemma 4.1, Eq. (4.1)

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Basic

namespace CaiCandesShen.GeneralConvex

/-- Lemma 4.1, p. 1968: if `Z ∈ ∂f_τ(X)` and `Z' ∈ ∂f_τ(X')`, then
`⟨Z - Z', X - X'⟩ ≥ ‖X - X'‖_F²`. -/
theorem subgradient_strongly_monotone {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (X X' Z Z' : Mat n₁ n₂) (hZ : IsSubgradient (fτ τ) X Z) (hZ' : IsSubgradient (fτ τ) X' Z') :
    frobNorm (X - X') ^ 2 ≤ frobInner (Z - Z') (X - X') := by sorry

end CaiCandesShen.GeneralConvex
