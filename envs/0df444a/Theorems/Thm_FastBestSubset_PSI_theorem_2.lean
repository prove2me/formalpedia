-- Prove2me | Theorems.Thm_FastBestSubset_PSI_theorem_2
-- name    : FastBestSubset.PSI.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:11.853161+00:00
-- url     : https://prove2.me/theorems/4251144c-6e8b-45dc-aaaa-d25069c57fa7
-- title:
--   Theorem 2 — the support of the CDSS iterates stabilizes and the iterates converge to a CW minimum with that support
-- statement:
--   Consider Problem (2), $\min_\beta F(\beta)=f(\beta)+\lambda_0\|\beta\|_0$ with $f(\beta)=\tfrac12\|y-X\beta\|^2+\lambda_1\|\beta\|_1+\lambda_2\|\beta\|_2^2$. Assume the columns of $X\in\mathbb R^{n\times p}$ have unit $L_2$ norm, $p\ge1$, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ and $\lambda_1=0$ or $\lambda_2=0$. This covers the (L0), (L0L1) and (L0L2) problems. For the (L0) and (L0L1) problems ($\lambda_2=0$), assume also Assumption 1, and Assumption 2 on the initial point $\beta^0$ when $p>n$.
--
--   Let $\{\beta^k\}$ be the iterates of Algorithm 1 (CDSS) with a positive integer parameter $C$, started at $\beta^0$. Then:
--
--   1. the support of $\{\beta^k\}$ stabilizes after finitely many iterations: there are an integer $m$ and a support $S$ with $\operatorname{Supp}(\beta^k)=S$ for all $k\ge m$;
--   2. the sequence $\{\beta^k\}$ converges to a CW minimum $B$ with $\operatorname{Supp}(B)=S$:
--   $$\beta^k\to B,\qquad B\ \text{is a CW minimum of (2)},\qquad \operatorname{Supp}(B)=S .$$
--
--   This is the convergence theorem for CDSS. Algorithm 2 calls Algorithm 1 at every iteration, and the proof of Theorem 4 uses this theorem to know that each call has an output, and that the output is a CW minimum.
--
--   **Formalization Note** The theorem restates the goal of the companion mission on Algorithm 1 for this mission's definitions. The scope $\lambda_1=0\lor\lambda_2=0$ restricts to the three problems the paper names. Assumptions 1–2 are bundled as one hypothesis that applies only when $\lambda_2=0$, matching "these assumptions are not needed for problem (L0L2)" (p. 12). Convergence in the product topology on $\mathbb R^p$ is Euclidean convergence.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Theorem 2, p. 12

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.PSI

/-- Theorem 2 (p. 12): for Algorithm 1 on the (L0), (L0L1) and (L0L2) problems (with
Assumptions 1–2 for (L0) and (L0L1)): (1) the support of `{βᵏ}` stabilizes, `Supp(βᵏ) = S` for
all `k ≥ m`; (2) `{βᵏ}` converges to a CW minimum `B` with `Supp(B) = S`. -/
theorem theorem_2 {n p : ℕ} [NeZero p] (D : FastBestSubset.CDSS.Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (FastBestSubset.CDSS.Assumption1 D ∧ (n < p → FastBestSubset.CDSS.Assumption2 D β0))) :
    ∃ (m : ℕ) (S : Finset (Fin p)),
      (∀ k ≥ m, FastBestSubset.CDSS.supp (FastBestSubset.CDSS.iter D C β0 k) = S) ∧
      ∃ B : Fin p → ℝ, Tendsto (FastBestSubset.CDSS.iter D C β0) atTop (𝓝 B) ∧ FastBestSubset.CDSS.IsCWMin D B ∧ FastBestSubset.CDSS.supp B = S := by sorry

end FastBestSubset.PSI
