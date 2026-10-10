-- Prove2me | Theorems.Thm_FRBSplitting_Linear_b_nonneg
-- name    : FRBSplitting.Linear.b_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:09.965418+00:00
-- url     : https://prove2.me/theorems/e3cd0e74-9147-474d-b470-f9d7393062b7
-- title:
--   Proof of Theorem 2.9, p. 9 — b_k ≥ 0 for L-Lipschitz B and λ ∈ (0, 1/(2L))
-- statement:
--   Let $H$ be a real inner product space, $B:H\to H$ $L$-Lipschitz with $L>0$, $\lambda\in(0,\tfrac1{2L})$, $(x_k)_{k\ge-1}$ any sequence in $H$ and $x\in H$ any point. Then for every $k\in\mathbb N$
--   $$b_k:=\tfrac12\|x_k-x\|^2+2\lambda\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2\ \ge\ 0 .$$
--
--   Nonnegativity of $b_k$ is what allows the inequality $\alpha(a_{k+1}+b_{k+1})\le a_k+b_k$ to be iterated into a bound on $a_{k+1}=\tfrac12\|x_{k+1}-x\|^2$ alone.
--
--   **Formalization Note.** Indices are shifted by one (`bSeq B lam x xs k` is $b_k$). The paper states the bound for the iterates of the method and a zero $x$; it holds for every sequence and every point, and is stated so (a stronger statement). $L>0$ is pinned because the step range divides by $L$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 9, definition of b_k and its lower bound, proof of Theorem 2.9

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linear

theorem b_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (L lam : ℝ)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / (2 * L))
    (x : ℕ → H) (xs : H) :
    ∀ k : ℕ, 0 ≤ bSeq B lam x xs k := by sorry

end FRBSplitting.Linear
