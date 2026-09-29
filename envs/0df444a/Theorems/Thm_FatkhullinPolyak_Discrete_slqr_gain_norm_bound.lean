-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_slqr_gain_norm_bound
-- name    : FatkhullinPolyak.Discrete.slqr_gain_norm_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:40:45.368539+00:00
-- url     : https://prove2.me/theorems/294a412e-d6da-4e3c-abb1-e41ca77a072a
-- title:
--   Lemma C.3 — for state feedback, $\|K\|_F\le 2\|B\|f(K)/(\lambda_1(\Sigma)\lambda_1(R))+\|A\|/\|B\|$
-- statement:
--   Consider state feedback, $C=I$ (so $r=n$). Assume $Q,R,\Sigma\succ0$ and $B\ne0$. For every stabilizing gain $K\in\mathcal S$,
--   $$\|K\|_F\le\frac{2\|B\|\,f(K)}{\lambda_1(\Sigma)\lambda_1(R)}+\frac{\|A\|}{\|B\|}, \tag{C.8}$$
--   where $\|\cdot\|$ is the spectral norm. In particular $\|K\|_F$ is bounded on every set where $f$ is bounded.
--
--   On $\mathcal S_0$ this gives an explicit bound on $\|K\|_F$ in terms of $f(K_0)$, which enters the LPL constant (3.11).
--
--   **Formalization Note** The lemma sits in Appendix C, "Analysis of SLQR", and its proof uses (3.2) with $\lambda_1(CC^\top)=1$ and $\|C\|=1$; it is stated for $C=I$.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 18, Lemma C.3, (C.8) (Appendix C: Analysis of SLQR)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma C.3 (p. 18), state feedback `C = I`: for `K ∈ S`,
(C.8) `‖K‖_F ≤ 2‖B‖f(K) / (λ₁(Σ)λ₁(R)) + ‖A‖/‖B‖`. -/
theorem slqr_gain_norm_bound {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin n) ℝ) (hK : K ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ)) :
    frobNorm K ≤ 2 * specNorm B * lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K / (lamMin Sig * lamMin R)
      + specNorm A / specNorm B := by sorry

end FatkhullinPolyak.Discrete
