-- Prove2me | Theorems.Thm_ApproxOLO_FullInfo_lemma_5
-- name    : ApproxOLO.FullInfo.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:34.889001+00:00
-- url     : https://prove2.me/theorems/8d84694c-121e-4661-baf4-26bfd439971c
-- title:
--   Lemma 5, pp. 9–10 — the ellipsoid separation-or-decomposition procedure returns a margin-ε separator or a 3ε-close convex combination of oracle outputs
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $d\ge2$, let $\mathcal K,\mathcal F,R,F,C$ be an instance, $\mathcal O_{\mathcal K}$ an $\alpha$-approximation oracle ($\alpha>0$), $x\in\mathbb R^d$, $\varepsilon\in(0,(\alpha+2)R]$, and $N$ a positive integer with
--   $$N\ge c\,d^2\ln\Big(\frac{(\alpha+1)R+\|x\|}{\varepsilon}\Big).$$
--   Run the Ellipsoid method for $N$ iterations on the feasibility problem
--   $$\text{find }w\in\mathbb R^d:\quad (x-z)\cdot w\ge\varepsilon\ \ \forall z\in\alpha\mathcal K,\qquad\|w\|\le1,\tag{4}$$
--   where each iteration, at the current center $w$, queries $(v,s)=\hat{\mathcal O}_{\mathcal K}(-w)$, cuts with $v-x$ if $(x-v)\cdot w<\varepsilon$, otherwise cuts with $w$ if $\|w\|>1$, and otherwise declares (4) feasible.
--
--   1. If the method declares (4) feasible at some iteration, the center $w$ of that iteration is a feasible solution of (4).
--   2. If it completes $N$ iterations without declaring feasibility, let $v_1,\dots,v_N$ be the oracle outputs gathered and $(a_1,\dots,a_N)$ any optimal solution of Problem (5). Then $p=\sum_{i=1}^Na_iv_i$ satisfies
--   $$\|x-p\|\le3\varepsilon.$$
--
--   So, with a number of oracle calls logarithmic in the scale, one either separates $x$ from $\mathrm{CH}(\alpha\mathcal K)$ with margin $\varepsilon$ or writes a point $3\varepsilon$-close to $x$ as a convex combination of extended-oracle outputs.
--
--   **Formalization Note** The constant $c$ is quantified once, before the dimension and the instance. The Ellipsoid method is fixed as: start at the unit ball $\mathcal B(0,1)$, standard central-cut update (the reused `LinearOptimization` update formulas, cut vectors $x-v$ and $-w$ in their sign convention); the paper only cites "the well known Ellipsoid method". $d\ge2$ is required because the central-cut update has the factor $d^2/(d^2-1)$. The feasibility claim is stated for every iteration at which the method would declare feasibility, which includes the first one (the one returned). $\|\cdot\|$ is Euclidean.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, pp. 9–10, Lemma 5 (Problems (4) and (5))

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model

namespace ApproxOLO.FullInfo

open Matrix

/-- **Lemma 5 (Separation-or-Decomposition via the Ellipsoid method), Garber,
arXiv:1709.03093v1, pp. 9–10.** There is a universal constant `c > 0` such that the following
holds for every `d ≥ 2`, instance, `α > 0`, oracle, `x ∈ ℝ^d`, `ε ∈ (0, (α + 2)R]` and positive
integer `N ≥ c d² ln(((α+1)R + ‖x‖)/ε)`. Run the Ellipsoid method of Lemma 5 on Problem (4)
(from `B(0, 1)`) for `N` iterations.
* If it declares Problem (4) feasible at iteration `k < N`, the iterate `w_k` is a feasible
  solution of (4): `(x − z) · w_k ≥ ε` for all `z ∈ αK`, and `‖w_k‖ ≤ 1`.
* If it completes `N` iterations without declaring feasibility, then for every optimal solution
  `(a_1, …, a_N)` of Problem (5) over the gathered oracle outputs `v_1, …, v_N`, the point
  `p = Σ_i a_i v_i` satisfies `‖x − p‖ ≤ 3ε`. -/
theorem lemma_5 : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d →
    ∀ (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d) (x : Vec d) (eps : ℝ)
      (N : ℕ),
    IsInstance K Fs R Fb C → 0 < alpha → IsApproxOracle K alpha O →
    0 < eps → eps ≤ (alpha + 2) * R → 1 ≤ N →
    c * (d : ℝ) ^ 2 * Real.log (((alpha + 1) * R + euclNorm x) / eps) ≤ (N : ℝ) →
    (∀ k < N, ellFeasibleAt O alpha R x eps k →
      (∀ z ∈ K, eps ≤ (x - alpha • z) ⬝ᵥ (ellIter O alpha R x eps k).1) ∧
        euclNorm (ellIter O alpha R x eps k).1 ≤ 1) ∧
    ((∀ k < N, ¬ ellFeasibleAt O alpha R x eps k) →
      ∀ a : Fin N → ℝ, IsSimplexOpt (fun i => (ellOut O alpha R x eps i).1) x a →
        euclNorm (x - ∑ i, a i • (ellOut O alpha R x eps i).1) ≤ 3 * eps) := by sorry

end ApproxOLO.FullInfo
