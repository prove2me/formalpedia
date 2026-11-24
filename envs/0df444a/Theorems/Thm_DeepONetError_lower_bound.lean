-- Prove2me | Theorems.Thm_DeepONetError_lower_bound
-- name    : DeepONetError.lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:27:30.223509+00:00
-- url     : https://prove2.me/theorems/74339c09-c880-4aae-9acd-9ef06df61ff6
-- title:
--   Theorem 3.6: lower bound on the reconstruction and total errors
-- statement:
--   Consider the setting of Definition 2.1. Let $\mathcal{N}=\mathcal{R}\circ\mathcal{A}\circ\mathcal{E}$ be a DeepONet with an encoder $\mathcal{E}:X\to\mathbb{R}^m$ and an approximator $\mathcal{A}:\mathbb{R}^m\to\mathbb{R}^p$. Its reconstruction $\mathcal{R}(\alpha)=\tau_0+\sum_{k=1}^p\alpha_k\tau_k$ has $\tau_0\in L^2(U)$ and linearly independent $\tau_1,\dots,\tau_p\in L^2(U)$. Let $\mathcal{P}$ be the optimal affine projection (3.19) associated with $\mathcal{R}$. Let $\lambda_1\ge\lambda_2\ge\cdots$ be the eigenvalues, repeated according to multiplicity, of the covariance operator $\Gamma_{\mathcal{G}_\#\mu}$ of the push-forward measure. Then
--
--   $$\sqrt{\sum_{k>p}\lambda_k}\le\widehat{\mathcal{E}}_{\mathcal{R}}\le\widehat{\mathcal{E}}.$$
--
--   No DeepONet with $p$ trunk functions can therefore beat the tail of the spectrum of $\Gamma_{\mathcal{G}_\#\mu}$.
--
--   **Formalization Note** The eigenvalues are given by a spectral decomposition $\Gamma_{\mathcal{G}_\#\mu}=\sum_k\lambda_k\phi_k\otimes\phi_k$, indexed from $0$. The paper's "optimal affine projection associated with $\mathcal{R}$" is the projector of Lemma 3.13, which presupposes linearly independent $\tau_1,\dots,\tau_p$; this is made an explicit hypothesis. Encoder and approximator are arbitrary maps.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.2.2, Theorem 3.6, eq. (3.9), p. 13; proof in Section 3.4, eq. (3.24), p. 20

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem lower_bound {d n m p : ℕ} {Dset : Set (Fin d → ℝ)} {U : Set (Fin n → ℝ)}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (L2 U)] [BorelSpace (L2 U)]
    (iota : X →L[ℝ] L2 Dset) (mu : Measure X) (A : Set X) (G : X → L2 U)
    (hdata : IsDeepONetData Dset U iota mu A G)
    (E : X → EuclideanSpace ℝ (Fin m))
    (Apx : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin p))
    (tau : Fin (p + 1) → L2 U) (htau : LinearIndependent ℝ (fun k : Fin p => tau k.succ))
    (lam : ℕ → ℝ) (phi : ℕ → L2 U) (hspec : IsSpectralDecomp (covOp (mu.map G)) lam phi) :
    (∑' k, ENNReal.ofReal (lam (k + p))) ^ ((1 : ℝ) / 2) ≤
        recErr (mu.map G) (trunkRec tau) (optProj tau) ∧
      recErr (mu.map G) (trunkRec tau) (optProj tau) ≤
        totalErr mu G (fun u => trunkRec tau (Apx (E u))) := by sorry

end DeepONetError
