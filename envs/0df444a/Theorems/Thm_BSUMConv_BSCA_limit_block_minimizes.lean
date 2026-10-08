-- Prove2me | Theorems.Thm_BSUMConv_BSCA_limit_block_minimizes
-- name    : BSUMConv.BSCA.limit_block_minimizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:53.01518+00:00
-- url     : https://prove2.me/theorems/9484a8b2-6eb1-415a-bb85-c19ef91a69c3
-- title:
--   After (39), p. 19 — the limit block minimizes its approximation
-- statement:
--   Along a subsequence updating block $k$, suppose $x^{r_q}\to z$ and $y^{r_q}-x^{r_q}\to0$. Each $y_k^{r_q}$ minimizes $h_k(\cdot,x^{r_q})$ over $X_k$. Joint continuity of the approximation then yields
--   $$h_k(z_k,z)\le h_k(w,z)\qquad\text{for every }w\in X_k.$$
--
--   This is the limiting block optimality statement used after (39).
--
--   **Formalization Note** Closed convex block sets and step sizes at most one ensure the subsequence and its limit stay feasible, where the stated `ContinuousOn` hypothesis applies.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 19, (39) and following display

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSCA_Setting

namespace BSUMConv.BSCA

open Filter Topology TsengBCD.Stationary

/-- From (39), p. 19: the limit block minimizes the limiting approximation. -/
theorem limit_block_minimizes {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (σ β αinit : ℝ) (x y : ℕ → X n) (j : ℕ → ℕ)
    (hclosed : ∀ i, IsClosed (Xs i)) (hconvXs : ∀ i, Convex ℝ (Xs i))
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αinit) (hα1 : αinit ≤ 1)
    (hcont : ContinuousApprox Xs h)
    (hrun : IsBSCARun Xs f h s σ β αinit x y j)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : X n)
    (hz : Tendsto (fun q => x (φ q)) atTop (𝓝 z))
    (hd : Tendsto (fun q => y (φ q) - x (φ q)) atTop (𝓝 0))
    (k : Fin N) (hk : ∀ q, s (φ q) = k) :
    ∀ w ∈ Xs k, h k (z k) z ≤ h k w z := by sorry

end BSUMConv.BSCA
