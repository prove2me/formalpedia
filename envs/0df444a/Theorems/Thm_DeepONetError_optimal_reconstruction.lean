-- Prove2me | Theorems.Thm_DeepONetError_optimal_reconstruction
-- name    : DeepONetError.optimal_reconstruction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:26:26.573217+00:00
-- url     : https://prove2.me/theorems/e2c05b11-1eae-4b11-96a5-9c07c431e8a6
-- title:
--   Theorem 3.14: the optimal affine reconstruction
-- statement:
--   Let $\mu$ be a probability measure on $X$, let $\mathcal{G}:X\to L^2(U)$ be measurable with $\int\|\mathcal{G}(u)\|^2_{L^2(U)}d\mu<\infty$, and let $\nu=\mathcal{G}_\#\mu$. Let $\Gamma=\int(v-\mathbb{E}_\nu[v])\otimes(v-\mathbb{E}_\nu[v])\,d\nu=\sum_k\lambda_k\phi_k\otimes\phi_k$, with orthonormal eigenvectors $\phi_k$ and eigenvalues $\lambda_1\ge\lambda_2\ge\cdots$. Put
--   $$\mathcal{R}_{\mathrm{opt}}(\alpha)=\hat\tau_0+\sum_{j=1}^p\alpha_j\hat\tau_j,\qquad\hat\tau_0=\mathbb{E}_\nu[v],\ \hat\tau_j=\phi_j,$$
--   $$\mathcal{P}(v)=\big(\langle v-\hat\tau_0,\hat\tau_1\rangle,\dots,\langle v-\hat\tau_0,\hat\tau_p\rangle\big).$$
--   Then:
--   1. For every affine reconstruction $\mathcal{R}=\mathcal{R}_{\boldsymbol\tau}$ with $\tau_0,\dots,\tau_p\in L^2(U)$ and every measurable $\mathcal{P}':L^2(U)\to\mathbb{R}^p$, the reconstruction error of $(\mathcal{R}_{\mathrm{opt}},\mathcal{P})$ is at most that of $(\mathcal{R},\mathcal{P}')$.
--   2. The optimal reconstruction error satisfies
--   $$\widehat{\mathcal{E}}_{\mathcal{R}_{\mathrm{opt}}}\ge\sqrt{\sum_{k>p}\lambda_k}.$$
--
--   **Formalization Note** The paper's "$p$ eigenvectors corresponding to the $p$ largest eigenvalues" are the first $p$ elements $\phi$ `0`, …, $\phi$ `(p-1)` of the spectral decomposition. Every orthonormal choice of top eigenvectors extends to such a decomposition. The bound (3.22) is stated as printed ($\ge$); by Theorem 3.12 it is an equality.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.4, Theorem 3.14, eqs. (3.21)-(3.23), p. 20

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem optimal_reconstruction {n p : ℕ} {U : Set (Fin n → ℝ)}
    [MeasurableSpace (L2 U)] [BorelSpace (L2 U)]
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (G : X → L2 U) (hG : Measurable G) (hG2 : (∫⁻ u, ‖G u‖ₑ ^ 2 ∂mu) < ⊤)
    (lam : ℕ → ℝ) (phi : ℕ → L2 U) (hspec : IsSpectralDecomp (covOp (mu.map G)) lam phi) :
    (∀ (tau : Fin (p + 1) → L2 U) (Proj : L2 U → EuclideanSpace ℝ (Fin p)), Measurable Proj →
      recErr (mu.map G) (trunkRec (optTrunk (mu.map G) phi))
          (fun v => WithLp.toLp 2 (fun k : Fin p => inner ℝ (v - mean (mu.map G)) (phi k))) ≤
        recErr (mu.map G) (trunkRec tau) Proj) ∧
    (∑' k, ENNReal.ofReal (lam (k + p))) ^ ((1 : ℝ) / 2) ≤
      recErr (mu.map G) (trunkRec (optTrunk (mu.map G) phi))
        (fun v => WithLp.toLp 2 (fun k : Fin p => inner ℝ (v - mean (mu.map G)) (phi k))) := by sorry

end DeepONetError
