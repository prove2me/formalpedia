-- Prove2me | Theorems.Thm_FRBSplitting_Linear_alpha_contraction
-- name    : FRBSplitting.Linear.alpha_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:56.572806+00:00
-- url     : https://prove2.me/theorems/d6a398af-bce2-4662-bf93-44cb5328b257
-- title:
--   Proof of Theorem 2.9, p. 9 — α(a_{k+1} + b_{k+1}) ≤ a_k + b_k with α = min{1 + 4mλ − 3ε/4, 1 + ε/2} > 1
-- statement:
--   Under the hypotheses of (27) ($A$ $m$-strongly monotone with $m>0$ and resolvents $J_{\gamma A}$, $B$ monotone and $L$-Lipschitz with $L>0$, $\lambda\in(0,\tfrac1{2L})$, $(x_k)_{k\ge-1}$ a run of $x_{k+1}=J_{\lambda A}(x_k-2\lambda B(x_k)+\lambda B(x_{k-1}))$, $x\in(A+B)^{-1}(0)$), put
--   $$\varepsilon:=\min\{\tfrac12-\lambda L,\ 5m\lambda\},\qquad \alpha:=\min\{1+4m\lambda-\tfrac{3\varepsilon}4,\ 1+\tfrac\varepsilon2\}.$$
--   Then $\alpha>1$ and for every $k\in\mathbb N$
--   $$\alpha\,(a_{k+1}+b_{k+1})\le a_k+b_k,$$
--   with $a_k=\tfrac12\|x_k-x\|^2$ and $b_k=\tfrac12\|x_k-x\|^2+2\lambda\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2$.
--
--   This one-step contraction of the energy $a_k+b_k$ by the fixed factor $\alpha>1$ is the core of the linear rate.
--
--   **Formalization Note.** Indices are shifted by one (`aSeq`, `bSeq` at `k` are $a_k,b_k$). $\varepsilon$ and $\alpha$ are `let`-bound with the paper's exact formulas. The page derives the inequality by combining (27) with (28); the last inequality of (28) is not valid for every $\lambda\in(0,\tfrac1{2L})$, but the combined inequality stated here is, so (28) itself is not part of the mission. Maximality of $A$ and completeness of $H$ are dropped (not needed); $L>0$ is pinned.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 9, proof of Theorem 2.9, the sentence after (28)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linear

theorem alpha_contraction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
    1 < α ∧ ∀ k : ℕ, α * (aSeq x xs (k + 1) + bSeq B lam x xs (k + 1))
        ≤ aSeq x xs k + bSeq B lam x xs k := by sorry

end FRBSplitting.Linear
