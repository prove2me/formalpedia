-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_lyapY_eigen_upper
-- name    : FatkhullinPolyak.Discrete.lyapY_eigen_upper
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:40:15.03066+00:00
-- url     : https://prove2.me/theorems/0443d9d1-50c9-485a-aac5-f08dd013cba0
-- title:
--   Lemma C.2 — $\lambda_n(Y)\le f(K)/\lambda_1(Q+C^\top K^\top RKC)$
-- statement:
--   Under the standing assumptions, let $K\in\mathcal S$ and let $Y=Y(K)$ solve
--   $$A_KY+YA_K^\top+\Sigma=0 .$$
--   Then
--   $$\lambda_n(Y)\le\frac{f(K)}{\lambda_1\big(Q+C^\top K^\top RKC\big)}. \tag{C.7}$$
--
--   Applied at the optimal gain, (C.7) bounds the factor $\lambda_n(Y_*)$ in Lemma C.1 by the optimal cost, which is how the LPL constant (3.11) is obtained.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 18, Lemma C.2, (C.7)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma C.2 (p. 18): for `K ∈ S` and `Y` the solution of `A_K Y + Y A_Kᵀ + Σ = 0`,
(C.7) `λₙ(Y) ≤ f(K) / λ₁(Q + CᵀKᵀRKC)`. -/
theorem lyapY_eigen_upper {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    lamMax (lyapY A B C Sig K) ≤
      lqrCost A B C Q R Sig K / lamMin (Q + C.transpose * K.transpose * R * K * C) := by sorry

end FatkhullinPolyak.Discrete
