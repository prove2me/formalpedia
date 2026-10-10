-- Prove2me | Theorems.Thm_FRBSplitting_Linesearch_eq_33
-- name    : FRBSplitting.Linesearch.eq_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:37.209274+00:00
-- url     : https://prove2.me/theorems/c71e2851-aa06-4e49-9bc5-ccc730fbe6c4
-- title:
--   (33), proof of Theorem 3.4, p. 11 — B is Lipschitz along the linesearch iterates
-- statement:
--   Let $H$ be a finite-dimensional real inner product space, $A:H\rightrightarrows H$ maximally monotone with resolvents $J_{tA}$, and $B:H\to H$ monotone and locally Lipschitz, with $(A+B)^{-1}(0)\neq\emptyset$. Let $\delta,\sigma\in(0,1)$ and let $(x_k)_{k\ge-1}$, $(\lambda_k)_{k\ge-1}$ be a run of Algorithm 1 with $\lambda_{-1}>0$. Then there is a constant $L>0$ such that
--   $$\|B(x_{k+1})-B(x_k)\|\le L\|x_{k+1}-x_k\|\qquad\forall k\in\mathbb N.$$
--
--   A locally Lipschitz map on a finite-dimensional space is Lipschitz on bounded sets, and the iterates are bounded; (33) replaces the global Lipschitz constant of Section 2 in the rest of the proof of Theorem 3.4.
--
--   **Formalization Note.** With the index shift (`x j` $=x_{j-1}$), paper $x_{k+1},x_k$ ($k\in\mathbb N$) are `x (k+2)`, `x (k+1)`. The constant $L$ is existential, quantified after the run, as on the page.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 11, proof of Theorem 3.4, (33)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linesearch_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linesearch

theorem eq_33 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B) (hBloc : LocallyLipschitz B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (lam : ℕ → ℝ) (x : ℕ → H) (hlam0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x) :
    ∃ L : ℝ, 0 < L ∧ ∀ k : ℕ, ‖B (x (k + 2)) - B (x (k + 1))‖ ≤ L * ‖x (k + 2) - x (k + 1)‖ := by sorry

end FRBSplitting.Linesearch
