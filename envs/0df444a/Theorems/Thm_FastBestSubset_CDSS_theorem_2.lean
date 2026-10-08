-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_theorem_2
-- name    : FastBestSubset.CDSS.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:19.601178+00:00
-- url     : https://prove2.me/theorems/bb2d7c94-392a-4935-bb71-29a3c90547e5
-- title:
--   Theorem 2 — the support of the CDSS iterates stabilizes and {βᵏ} converges to a CW minimum
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, $y\in\mathbb R^n$, $\lambda_0>0$, and $\lambda_1,\lambda_2\ge0$ with $\lambda_1=0$ or $\lambda_2=0$, so that Problem (2) is one of (L0), (L0L1), (L0L2). For (L0) and (L0L1) ($\lambda_2=0$) assume that every $\min\{n,p\}$ columns of $X$ are linearly independent (Assumption 1) and, when $p>n$, that $\beta^0$ satisfies Assumption 2. Let $C$ be a positive integer and $\{\beta^k\}$ the iterates of Algorithm 1 (cyclic coordinate descent with spacer steps) started at $\beta^0$. Then:
--
--   1. The support stabilizes after finitely many iterations: there are an integer $m$ and a support $S$ with $\mathrm{Supp}(\beta^k)=S$ for all $k\ge m$.
--   2. The sequence converges, $\beta^k\to B$, to a CW minimum $B$ of Problem (2) with $\mathrm{Supp}(B)=S$.
--
--   $$\exists\,m,\,S:\ \ \mathrm{Supp}(\beta^k)=S\ (k\ge m),\qquad \beta^k\to B,\quad B\ \text{CW minimum},\quad \mathrm{Supp}(B)=S .$$
--
--   This is the main convergence result for exact cyclic coordinate descent on the discontinuous $L_0$-penalized objective; no step-size or sufficient-decrease condition is imposed.
--
--   **Formalization Note** The iterates are those of the deterministic CDSS state machine of the Setting file, whose counting index includes spacer steps. Convergence is in the product topology on `Fin p → ℝ`, which coincides with the Euclidean one. The case $\lambda_1,\lambda_2>0$, which the paper never names, is excluded.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Theorem 2, p. 12 (proof §A.6, pp. 37–44)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Theorem 2 (p. 12): for Algorithm 1 on the (L0), (L0L1) and (L0L2) problems (with
Assumptions 1–2 for (L0) and (L0L1)): (1) the support of `{βᵏ}` stabilizes, `Supp(βᵏ) = S` for
all `k ≥ m`; (2) `{βᵏ}` converges to a CW minimum `B` with `Supp(B) = S`. -/
theorem theorem_2 {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (Assumption1 D ∧ (n < p → Assumption2 D β0))) :
    ∃ (m : ℕ) (S : Finset (Fin p)),
      (∀ k ≥ m, supp (iter D C β0 k) = S) ∧
      ∃ B : Fin p → ℝ, Tendsto (iter D C β0) atTop (𝓝 B) ∧ IsCWMin D B ∧ supp B = S := by sorry

end FastBestSubset.CDSS
