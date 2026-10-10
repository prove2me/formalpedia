-- Prove2me | Theorems.Thm_FRBSplitting_Linear_eq_27
-- name    : FRBSplitting.Linear.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:00.35402+00:00
-- url     : https://prove2.me/theorems/60afdf3e-a09b-46a9-9fd9-4f78dfbea0fb
-- title:
--   (27), p. 9 — (1 + 4mλ)a_{k+1} + b_{k+1} + ε‖x_{k+1} − x_k‖² ≤ a_k + b_k with ε = min{½ − λL, 5mλ} > 0
-- statement:
--   Under the hypotheses of Theorem 2.9 without maximality of $A$ ($H$ a real inner product space, $A$ $m$-strongly monotone with $m>0$ with resolvents $J_{\gamma A}$, $B$ monotone and $L$-Lipschitz with $L>0$, $\lambda\in(0,\tfrac1{2L})$, $(x_k)_{k\ge-1}$ a run of the constant-step method $x_{k+1}=J_{\lambda A}(x_k-2\lambda B(x_k)+\lambda B(x_{k-1}))$), let $x\in(A+B)^{-1}(0)$ and
--   $$\varepsilon:=\min\{\tfrac12-\lambda L,\ 5m\lambda\}.$$
--   Then $\varepsilon>0$ and for every $k\in\mathbb N$
--   $$(1+4m\lambda)a_{k+1}+b_{k+1}+\varepsilon\|x_{k+1}-x_k\|^2\le a_k+b_k,$$
--   where $a_k=\tfrac12\|x_k-x\|^2$ and $b_k=\tfrac12\|x_k-x\|^2+2\lambda\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2$.
--
--   This is the energy inequality of the proof of Theorem 2.9 rewritten in terms of the two sequences $(a_k)$, $(b_k)$, the form in which it is iterated.
--
--   **Formalization Note.** Indices are shifted by one: `aSeq x xs k`, `bSeq B lam x xs k` are $a_k,b_k$ and `x (k+2) - x (k+1)` is $x_{k+1}-x_k$. $\varepsilon$ is introduced by a `let` with the paper's exact formula. Maximality of $A$ and completeness of $H$ are dropped (not needed); $L>0$ is pinned.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 9, (27)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linear

theorem eq_27 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (m L lam : ℝ)
    (hm : 0 < m) (hAs : IsStronglyMonotoneOp m A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / (2 * L))
    (x : ℕ → H) (hrun : FRBSplitting.Weak.IsFRBRun J B (fun _ => lam) x)
    (xs : H) (hxs : xs ∈ FRBSplitting.Weak.zeroSet A B) :
    let ε := min (1 / 2 - lam * L) (5 * m * lam)
    0 < ε ∧ ∀ k : ℕ, (1 + 4 * m * lam) * aSeq x xs (k + 1) + bSeq B lam x xs (k + 1)
        + ε * ‖x (k + 2) - x (k + 1)‖ ^ 2 ≤ aSeq x xs k + bSeq B lam x xs k := by sorry

end FRBSplitting.Linear
