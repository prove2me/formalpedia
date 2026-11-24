-- Prove2me | Theorems.Thm_DeepONetError_reconstruction_error_trunk_approx
-- name    : DeepONetError.reconstruction_error_trunk_approx
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:28:45.125311+00:00
-- url     : https://prove2.me/theorems/896a943a-d5b0-42e7-8be4-b0f20ae401a7
-- title:
--   Proposition 3.15: reconstruction error of approximate eigenfunctions
-- statement:
--   Let $\nu\in\mathcal{P}_2(L^2(U))$, and write its covariance operator as $\Gamma_\nu=\sum_{k\ge1}\lambda_k\,\phi_k\otimes\phi_k$ with $\lambda_1\ge\lambda_2\ge\cdots$ and orthonormal $\phi_k$. Let $\hat\tau_0=\mathbb{E}_\nu[v]$ and $\hat\tau_k=\phi_k$ for $k=1,\dots,p$. Let $\tau_0,\dots,\tau_p\in L^2(U)$ with $\tau_1,\dots,\tau_p$ linearly independent, let $\mathcal{R}(\alpha)=\tau_0+\sum_k\alpha_k\tau_k$, and let $\mathcal{P}$ be its optimal projection (3.19). Then
--
--   $$\widehat{\mathcal{E}}_{\mathcal{R}}\le\sqrt{1+\mathrm{Tr}(\Gamma_\nu)}\,\max_{k=0,\dots,p}\|\hat\tau_k-\tau_k\|_{L^2}+\sqrt{\sum_{k>p}\lambda_k},\qquad\mathrm{Tr}(\Gamma_\nu)=\sum_k\lambda_k.$$
--
--   Trunk networks that approximate the mean and the top eigenfunctions of the covariance operator therefore achieve a nearly optimal reconstruction error.
--
--   **Formalization Note** The trunk functions are arbitrary elements of $L^2(U)$, so trunk networks are a special case. Linear independence of $\tau_1,\dots,\tau_p$ is required for the projection (3.19) to be defined, and the paper presupposes it.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.4, Proposition 3.15, eq. (3.25), p. 21; proof in Appendix C.5, p. 86

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem reconstruction_error_trunk_approx {n p : ℕ} {U : Set (Fin n → ℝ)}
    [MeasurableSpace (L2 U)] [BorelSpace (L2 U)]
    (nu : Measure (L2 U)) (hnu : IsP2 nu)
    (lam : ℕ → ℝ) (phi : ℕ → L2 U) (hspec : IsSpectralDecomp (covOp nu) lam phi)
    (tau : Fin (p + 1) → L2 U) (htau : LinearIndependent ℝ (fun k : Fin p => tau k.succ)) :
    recErr nu (trunkRec tau) (optProj tau) ≤
      (1 + ∑' k, ENNReal.ofReal (lam k)) ^ ((1 : ℝ) / 2) *
          (⨆ k : Fin (p + 1), ‖optTrunk nu phi k - tau k‖ₑ) +
        (∑' k, ENNReal.ofReal (lam (k + p))) ^ ((1 : ℝ) / 2) := by sorry

end DeepONetError
