-- Prove2me | Theorems.Thm_FRBSplitting_Linear_a_le_geometric
-- name    : FRBSplitting.Linear.a_le_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:06.505055+00:00
-- url     : https://prove2.me/theorems/3cb13c0b-4cba-4e97-95e4-3e8984cc5717
-- title:
--   Proof of Theorem 2.9, p. 9 — a_{k+1} ≤ a_{k+1} + b_{k+1} ≤ (a_0 + b_0)/α^{k+1}
-- statement:
--   Under the hypotheses of (27), with $\varepsilon:=\min\{\tfrac12-\lambda L,5m\lambda\}$ and $\alpha:=\min\{1+4m\lambda-\tfrac{3\varepsilon}4,1+\tfrac\varepsilon2\}$ as in the proof of Theorem 2.9, for every $k\in\mathbb N$
--   $$a_{k+1}\le a_{k+1}+b_{k+1}\le\frac1{\alpha^{k+1}}\,(a_0+b_0),$$
--   where $a_k=\tfrac12\|x_k-x\|^2$, $b_k=\tfrac12\|x_k-x\|^2+2\lambda\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2$ and $x\in(A+B)^{-1}(0)$.
--
--   Since $\alpha>1$, this bounds $\|x_{k+1}-x\|^2=2a_{k+1}$ by a geometric sequence, which is the R-linear convergence of Theorem 2.9.
--
--   **Formalization Note.** Indices are shifted by one (`aSeq x xs 0`, `bSeq B lam x xs 0` are $a_0,b_0$, built from $x_0$ and $x_{-1}$). $\varepsilon$ and $\alpha$ are `let`-bound with the paper's formulas; the division is a real division by $\alpha^{k+1}>0$. Maximality of $A$ and completeness of $H$ are dropped (not needed); $L>0$ is pinned.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 9, proof of Theorem 2.9, iterated inequality

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linear

theorem a_le_geometric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (m L lam : ℝ)
    (hm : 0 < m) (hAs : IsStronglyMonotoneOp m A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / (2 * L))
    (x : ℕ → H) (hrun : FRBSplitting.Weak.IsFRBRun J B (fun _ => lam) x)
    (xs : H) (hxs : xs ∈ FRBSplitting.Weak.zeroSet A B) :
    let ε := min (1 / 2 - lam * L) (5 * m * lam)
    let α := min (1 + 4 * m * lam - 3 * ε / 4) (1 + ε / 2)
    ∀ k : ℕ, aSeq x xs (k + 1) ≤ aSeq x xs (k + 1) + bSeq B lam x xs (k + 1)
      ∧ aSeq x xs (k + 1) + bSeq B lam x xs (k + 1) ≤ (aSeq x xs 0 + bSeq B lam x xs 0) / α ^ (k + 1) := by sorry

end FRBSplitting.Linear
