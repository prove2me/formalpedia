-- Prove2me | Theorems.Thm_DeepONetError_optimal_affine_subspace
-- name    : DeepONetError.optimal_affine_subspace
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:24:43.912694+00:00
-- url     : https://prove2.me/theorems/2ccd7ab8-1b3d-451c-a5c5-fa2aa42c2883
-- title:
--   Theorem 3.12: optimal affine subspaces and the projection error
-- statement:
--   Let $H$ be a separable real Hilbert space, $\nu\in\mathcal{P}_2(H)$ and $p\ge1$. Let $\Gamma=\int_H(v-\mathbb{E}[v])\otimes(v-\mathbb{E}[v])\,d\nu(v)$ be the covariance operator, with eigenvalues $\lambda_1\ge\lambda_2\ge\cdots$ repeated according to multiplicity, and let $\hat V_0$ be an affine subspace whose direction $\hat V$ has dimension $p$. Then:
--   1. There is a unique $\hat v_0\in\hat V_0$ with $\|\mathbb{E}[v]-\hat v_0\|=\inf_{\hat v\in\hat V_0}\|\mathbb{E}[v]-\hat v\|$.
--   2. For this $\hat v_0$,
--   $$\widehat{\mathcal{E}}_{\mathrm{Proj}}(\hat V_0)=\int_H\inf_{\hat v\in\hat V_0}\|v-\hat v\|^2d\nu=\|\mathbb{E}[v]-\hat v_0\|^2+\int_H\inf_{\hat v\in\hat V}\|v-\mathbb{E}[v]-\hat v\|^2d\nu(v).$$
--   3. Let $E_j$ be the eigenspaces of $\Gamma$ for its distinct eigenvalues, with $n$ chosen as in Theorem 3.10. Then $\hat V_0$ minimizes $\widehat{\mathcal{E}}_{\mathrm{Proj}}$ among affine subspaces of dimension $p$ if and only if
--   $$\hat v_0=\mathbb{E}[v]\quad\text{and}\quad\bigoplus_{j=1}^{n-1}E_j\subset\hat V\subset\bigoplus_{j=1}^nE_j.$$
--   4. In that case $\widehat{\mathcal{E}}_{\mathrm{Proj}}(\hat V_0)=\sum_{j>p}\lambda_j$.
--
--   This extends Theorem 3.10 to affine subspaces: the optimal affine space passes through the mean and is spanned by the top eigenvectors of the centered covariance.
--
--   **Formalization Note** The paper writes $\widehat{\mathcal{E}}_{\mathrm{Proj}}(\hat V)$ on the left of (3.17); the proof shows it is $\widehat{\mathcal{E}}_{\mathrm{Proj}}(\hat V_0)$. Eigenvalues come from a spectral decomposition indexed from $0$, as in Theorem 3.10.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.3, Theorem 3.12, eqs. (3.16)-(3.18), p. 18; proof in Appendix C.3.2, pp. 84-85

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem optimal_affine_subspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (nu : Measure H) (hnu : IsP2 nu)
    (lam : ℕ → ℝ) (phi : ℕ → H) (hspec : IsSpectralDecomp (covOp nu) lam phi)
    (p : ℕ) (hp : 1 ≤ p) (V0 : AffineSubspace ℝ H) (hV0 : Module.finrank ℝ V0.direction = p) :
    (∃! v0 : H, v0 ∈ V0 ∧ ∀ w ∈ V0, ‖mean nu - v0‖ ≤ ‖mean nu - w‖) ∧
    ∀ v0 ∈ V0, (∀ w ∈ V0, ‖mean nu - v0‖ ≤ ‖mean nu - w‖) →
      projErr nu (V0 : Set H) = ‖mean nu - v0‖ₑ ^ 2 +
          (∫⁻ v, Metric.infEDist (v - mean nu) (V0.direction : Set H) ^ 2 ∂nu) ∧
      (IsOptimalAffine nu p V0 ↔
        v0 = mean nu ∧ eigSpan (covOp nu) (Set.Ioi (lam (p - 1))) ≤ V0.direction ∧
          V0.direction ≤ eigSpan (covOp nu) (Set.Ici (lam (p - 1)))) ∧
      (IsOptimalAffine nu p V0 → projErr nu (V0 : Set H) = ∑' k, ENNReal.ofReal (lam (k + p))) := by sorry

end DeepONetError
