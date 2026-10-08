-- Prove2me | Theorems.Thm_BSUMConv_BSUM_eq_14
-- name    : BSUMConv.BSUM.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:28.994686+00:00
-- url     : https://prove2.me/theorems/a3cfd6d3-fbff-484e-b412-b80a5de9f52c
-- title:
--   (14), p. 10 — the BSUM objective values are non-increasing: f(x⁰) ≥ f(x¹) ≥ f(x²) ≥ …
-- statement:
--   Let $\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n$ with each $\mathcal X_i$ closed and convex, let $f$ be continuous on $\mathcal X$, and let the approximation functions $u_i$ satisfy Assumption 2 (B1)–(B4). Let $x^0,x^1,\dots$ be the iterates of the BSUM algorithm with the cyclic rule: $x^0\in\mathcal X$, and $x^{r+1}$ is obtained from $x^r$ by replacing the scheduled block $i$ by a minimiser of $u_i(\cdot,x^r)$ over $\mathcal X_i$. Then
--
--   $$f(x^0)\ \ge\ f(x^1)\ \ge\ f(x^2)\ \ge\ \cdots.$$
--
--   Monotonicity of the objective values is the first step of the convergence analysis of Theorem 2.
--
--   **Formalization Note** Stated as `Antitone (fun r => f (x r))`.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 10, proof of Theorem 2(a), display (14)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

namespace BSUMConv.BSUM

open TsengBCD.Stationary Filter Topology

/-- (14), p. 10: the objective values of a cyclic BSUM run are non-increasing,
`f(x⁰) ≥ f(x¹) ≥ f(x²) ≥ ⋯`. -/
theorem eq_14 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x) :
    Antitone (fun r => f (x r)) := by sorry

end BSUMConv.BSUM
