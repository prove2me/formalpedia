-- Prove2me | Theorems.Thm_DeepONetError_optimal_linear_subspace
-- name    : DeepONetError.optimal_linear_subspace
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:24:05.244232+00:00
-- url     : https://prove2.me/theorems/01cdf3a7-226e-4220-ac67-7c7ff1ccda8e
-- title:
--   Theorem 3.10: optimal linear subspaces and the projection error
-- statement:
--   Let $H$ be a separable real Hilbert space and $\nu\in\mathcal{P}_2(H)$. Let $\overline\Gamma=\int_Hv\otimes v\,d\nu(v)$ be the uncentered covariance operator, with eigenvalues $\lambda_1\ge\lambda_2\ge\cdots$ repeated according to multiplicity, and let $p\ge1$. For a subspace $\hat V$ let $\widehat{\mathcal{E}}_{\mathrm{Proj}}(\hat V)=\int_H\inf_{\hat v\in\hat V}\|v-\hat v\|^2d\nu(v)$. Then:
--   1. There is a $p$-dimensional subspace $V_p$ minimizing $\widehat{\mathcal{E}}_{\mathrm{Proj}}$ among all $p$-dimensional subspaces.
--   2. Let $E_1,E_2,\dots$ be the eigenspaces of $\overline\Gamma$ for its distinct eigenvalues $\overline\lambda_1>\overline\lambda_2>\cdots$, and choose $n$ with $\sum_{k<n}\dim E_k<p\le\sum_{k\le n}\dim E_k$, so that $\overline\lambda_n=\lambda_p$. A $p$-dimensional subspace $\hat V$ is optimal if and only if
--   $$\bigoplus_{k=1}^{n-1}E_k\subset\hat V\subset\bigoplus_{k=1}^nE_k.$$
--   3. If $p=\sum_{k\le n}\dim E_k$ for some $n$, equivalently $\lambda_{p+1}<\lambda_p$, the optimal $p$-dimensional subspace is unique.
--   4. Every optimal $p$-dimensional subspace $\hat V$ satisfies
--   $$\widehat{\mathcal{E}}_{\mathrm{Proj}}(\hat V)=\sum_{j>p}\lambda_j.$$
--
--   This is principal component analysis in a Hilbert space. It identifies the best $p$-dimensional linear subspace for a given measure.
--
--   **Formalization Note** The eigenvalues come from a spectral decomposition $\overline\Gamma=\sum_k\lambda_k\phi_k\otimes\phi_k$ with an orthonormal sequence indexed from $0$, so the paper's $\lambda_p$ is `lam (p-1)`. The orthonormal sequence makes $H$ infinite-dimensional. This is the case for every space to which the paper applies the theorem; for $\dim H<p$ the printed existence claim is false. The sums of eigenspaces are written as spans of eigenvectors with eigenvalue $>\lambda_p$, respectively $\ge\lambda_p$. The paper's "$\inf_{\hat V\subset V}$" is read as an infimum over subspaces of $H$.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.3, Theorem 3.10, eqs. (3.13)-(3.15), p. 17; proof in Appendix C.3, pp. 78-84

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem optimal_linear_subspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (nu : Measure H) (hnu : IsP2 nu)
    (lam : ℕ → ℝ) (phi : ℕ → H) (hspec : IsSpectralDecomp (uncovOp nu) lam phi)
    (p : ℕ) (hp : 1 ≤ p) :
    (∃ V : Submodule ℝ H, IsOptimalSubspace nu p V) ∧
    (∀ V : Submodule ℝ H, Module.finrank ℝ V = p →
      (IsOptimalSubspace nu p V ↔
        eigSpan (uncovOp nu) (Set.Ioi (lam (p - 1))) ≤ V ∧
          V ≤ eigSpan (uncovOp nu) (Set.Ici (lam (p - 1))))) ∧
    (lam p < lam (p - 1) → ∀ V W : Submodule ℝ H,
      IsOptimalSubspace nu p V → IsOptimalSubspace nu p W → V = W) ∧
    (∀ V : Submodule ℝ H, IsOptimalSubspace nu p V →
      projErr nu (V : Set H) = ∑' k, ENNReal.ofReal (lam (k + p))) := by sorry

end DeepONetError
