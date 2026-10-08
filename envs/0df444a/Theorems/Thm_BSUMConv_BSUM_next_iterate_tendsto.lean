-- Prove2me | Theorems.Thm_BSUMConv_BSUM_next_iterate_tendsto
-- name    : BSUMConv.BSUM.next_iterate_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:42.039333+00:00
-- url     : https://prove2.me/theorems/6c57d1d1-41c6-40bc-9c3c-f04ba4c7a485
-- title:
--   Proof of Theorem 2(a), pp. 11–12 — if x^{r_j} → z then x^{r_j+1} → z
-- statement:
--   In the setting of Theorem 2(a): closed convex blocks $\mathcal X_i$, $f$ continuous on $\mathcal X$, Assumption 2, each $u_i(x_i,y)$ quasi-convex in $x_i$ on $\mathcal X_i$ for every $y\in\mathcal X$, and the subproblem (13) has a unique solution at every point of $\mathcal X$ for every block. Let $(x^r)$ be the BSUM iterates under the cyclic rule, and let $r_1<r_2<\cdots$ be indices with $x^{r_j}\to z$. Then
--
--   $$x^{r_j+1}\ \longrightarrow\ z\qquad (j\to\infty).$$
--
--   This is the step where quasi-convexity and uniqueness of the block minimisers enter: it prevents the iterates from moving a fixed distance at every step near a limit point, and it lets the limit point be propagated through all blocks.
--
--   **Formalization Note** The paper proves this after restricting to indices at which the step $x^{r_j}\to x^{r_j+1}$ updates a fixed block; the statement here is for an arbitrary strictly increasing sequence of indices, which is what "Now we prove that $x^{r_j+1}\to z$" asserts and follows by splitting the indices by the block updated.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, pp. 11–12, proof of Theorem 2(a), the claim x^{r_j+1} → z

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

namespace BSUMConv.BSUM

open TsengBCD.Stationary Filter Topology

/-- Proof of Theorem 2(a), pp. 11–12: under quasi-convexity of the `u_i` in `x_i` and
uniqueness of the block minimisers, if a subsequence `x^{r_j}` of a cyclic BSUM run converges
to `z`, then so does `x^{r_j+1}`. -/
theorem next_iterate_tendsto {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (hqc : BlockQuasiconvex Xs u) (huniq : ∀ i, UniqueBlockMin Xs u i)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x)
    (z : X n) (φ : ℕ → ℕ) (hφ : StrictMono φ) (hlim : Tendsto (x ∘ φ) atTop (𝓝 z)) :
    Tendsto (fun j => x (φ j + 1)) atTop (𝓝 z) := by sorry

end BSUMConv.BSUM
