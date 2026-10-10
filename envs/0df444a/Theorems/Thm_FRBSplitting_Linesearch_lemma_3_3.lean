-- Prove2me | Theorems.Thm_FRBSplitting_Linesearch_lemma_3_3
-- name    : FRBSplitting.Linesearch.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:18.99201+00:00
-- url     : https://prove2.me/theorems/7e0b60fc-1601-491c-8ccb-de8e41480cec
-- title:
--   Lemma 3.3, p. 10 — the energy inequality (32) along runs of Algorithm 1 (for k ≥ 1)
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ monotone with resolvents $J_{tA}$, and $B:H\to H$ monotone. Let $\delta,\sigma\in(0,1)$, and let $(x_k)_{k\ge-1}$, $(\lambda_k)_{k\ge-1}$ be a run of Algorithm 1 with $\lambda_{-1}>0$. Let $x\in(A+B)^{-1}(0)$. Then there exists $\varepsilon>0$ such that for all $k\ge1$,
--   $$\|x_{k+1}-x\|^2+2\lambda_k\langle B(x_{k+1})-B(x_k),x-x_{k+1}\rangle+\Big(\tfrac12+\varepsilon\Big)\|x_{k+1}-x_k\|^2\le\|x_k-x\|^2+2\lambda_{k-1}\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2.$$
--
--   This is the analogue of the energy inequality of Lemma 2.4 for the linesearch variant: the linesearch test (30) takes the role of the Lipschitz constant of $B$. It drives the boundedness of the iterates in the proof of Theorem 3.4.
--
--   **Formalization Note.** The page states (32) "for all $k\in\mathbb N$". The proof uses (30) at step $k-1$, i.e. $\lambda_{k-1}\|B(x_k)-B(x_{k-1})\|\le\frac\delta2\|x_k-x_{k-1}\|$, which Algorithm 1 guarantees only for $k\ge1$; at $k=0$ it concerns the arbitrary initial data $x_0,x_{-1},\lambda_{-1}$, and (32) can fail there (e.g. $H=\mathbb R$, $A\equiv\{0\}$, $B(y)=cy$, $x=0$, $x_0=0$, $x_{-1}=1$, $\lambda_{-1}c=10$). The statement is therefore made for $k\ge1$, which is what the proof of Theorem 3.4 uses. With the index shift (`x j` $=x_{j-1}$, `lam j` $=\lambda_{j-1}$), paper $x_{k+2},x_{k+1},x_k,\lambda_{k+1},\lambda_k$ are `x (k+3)`, `x (k+2)`, `x (k+1)`, `lam (k+2)`, `lam (k+1)` for `k : ℕ`. Only monotonicity of $A$ is assumed (the proof uses no maximality), and no completeness of $H$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 10, Lemma 3.3, (32)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linesearch_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linesearch

theorem lemma_3_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMonotoneOp A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (lam : ℕ → ℝ) (x : ℕ → H) (hlam0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x)
    (xs : H) (hxs : xs ∈ FRBSplitting.Weak.zeroSet A B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ,
      ‖x (k + 3) - xs‖ ^ 2 + 2 * lam (k + 2) * ⟪B (x (k + 3)) - B (x (k + 2)), xs - x (k + 3)⟫_ℝ
          + (1 / 2 + ε) * ‖x (k + 3) - x (k + 2)‖ ^ 2 ≤
        ‖x (k + 2) - xs‖ ^ 2 + 2 * lam (k + 1) * ⟪B (x (k + 2)) - B (x (k + 1)), xs - x (k + 2)⟫_ℝ
          + 1 / 2 * ‖x (k + 2) - x (k + 1)‖ ^ 2 := by sorry

end FRBSplitting.Linesearch
