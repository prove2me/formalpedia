-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_lqrCost_coercive_bounds
-- name    : FatkhullinPolyak.Discrete.lqrCost_coercive_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:37:10.464542+00:00
-- url     : https://prove2.me/theorems/fa022b66-c9db-4090-8a95-6c864879aa40
-- title:
--   Lemma 3.8 — the LQR cost is coercive on $\mathcal S$, with lower bounds (3.1) and (3.2)
-- statement:
--   Under the standing assumptions ($Q,R,\Sigma\succ0$, $\operatorname{rank}C=r$, $B\ne0$), the LQR cost $f(K)=\mathrm{Tr}(X(K)\Sigma)$ on the stabilizing set $\mathcal S$ has the following properties.
--
--   1. $f$ is continuous on $\mathcal S$.
--   2. If $(K_j)\subseteq\mathcal S$ and $\|K_j\|_F\to\infty$, then $f(K_j)\to+\infty$.
--   3. If $(K_j)\subseteq\mathcal S$ and $K_j\to K$ with $K$ on the boundary $\partial\mathcal S$, then $f(K_j)\to+\infty$.
--   4. For every $K\in\mathcal S$,
--   $$f(K)\ge\frac{\lambda_1(\Sigma)\lambda_1(Q)}{-2\Re\lambda_n(A_K)}, \tag{3.1}$$
--   $$f(K)\ge\frac{\lambda_1(\Sigma)\lambda_1(R)\|K\|_F^2\,\lambda_1(CC^\top)}{2\|A\|+2\|K\|_F\|B\|\|C\|}, \tag{3.2}$$
--   where $\Re\lambda_n(A_K)$ is the largest real part of an eigenvalue of $A_K=A-BKC$ and $\|\cdot\|$ is the spectral norm.
--
--   Items 1–3 are the paper's Definition 3.7 of coercivity. Coercivity gives that sublevel sets are compact subsets of $\mathcal S$ (Corollaries 3.9 and 3.10), which is what makes a first-order method on this non-convex, unbounded domain analysable.
--
--   **Formalization Note** Coercivity is stated as its two limit clauses plus continuity, as in Definition 3.7. The unbounded clause is stated in the Frobenius norm; all norms on $\mathbb R^{m\times r}$ are equivalent, so this is the paper's $\|K_j\|\to\infty$.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 7, Definition 3.7 and Lemma 3.8, (3.1)–(3.2); standing assumptions p. 3

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma 3.8 (p. 7): `f` is coercive on `S` (continuous on `S`, and `f(Kⱼ) → +∞` along any
sequence in `S` with `‖Kⱼ‖ → ∞` or `Kⱼ → K ∈ ∂S`), and for every `K ∈ S`
(3.1) `f(K) ≥ λ₁(Σ)λ₁(Q) / (−2ℜλₙ(A_K))`,
(3.2) `f(K) ≥ λ₁(Σ)λ₁(R)‖K‖_F² λ₁(CCᵀ) / (2‖A‖ + 2‖K‖_F‖B‖‖C‖)`. -/
theorem lqrCost_coercive_bounds {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0) :
    ContinuousOn (lqrCost A B C Q R Sig) (stabSet A B C) ∧
    (∀ Ks : ℕ → Matrix (Fin m) (Fin r) ℝ, (∀ j, Ks j ∈ stabSet A B C) →
      Tendsto (fun j => frobNorm (Ks j)) atTop atTop →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ (Ks : ℕ → Matrix (Fin m) (Fin r) ℝ) (K : Matrix (Fin m) (Fin r) ℝ),
      (∀ j, Ks j ∈ stabSet A B C) → K ∈ frontier (stabSet A B C) →
      Tendsto Ks atTop (𝓝 K) →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ K ∈ stabSet A B C,
      lamMin Sig * lamMin Q / (-2 * maxRe (A - B * K * C)) ≤ lqrCost A B C Q R Sig K ∧
      lamMin Sig * lamMin R * frobNorm K ^ 2 * lamMin (C * C.transpose) /
          (2 * specNorm A + 2 * frobNorm K * specNorm B * specNorm C)
        ≤ lqrCost A B C Q R Sig K) := by sorry

end FatkhullinPolyak.Discrete
