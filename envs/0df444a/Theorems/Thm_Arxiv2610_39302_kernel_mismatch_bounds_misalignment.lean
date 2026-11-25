-- Prove2me | Theorems.Thm_Arxiv2610_39302_kernel_mismatch_bounds_misalignment
-- name    : Arxiv2610_39302.kernel_mismatch_bounds_misalignment
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:01:16.503874+00:00
-- url     : https://prove2.me/theorems/0bb4da83-4728-58a4-91a0-c8aff894f4cb
-- title:
--   Theorem 2: kernel mismatch bounds misalignment
-- statement:
--   Let $\pi_1,\pi_2$ be positive-pair laws on a finite world with the same marginal $p>0$, let $1\le k<|Z|$, and let $\Phi_1,\Phi_2$ be spectral embeddings of $\pi_1,\pi_2$ (any orthonormal top-$k$ eigenvectors if $K_{\pi_1}$ has ties). Suppose the eigengap $\delta=\mu_k-\mu_{k+1}$ of $K_{\pi_2}$ is positive, with $\mu_{|Z|}:=-\infty$. Then
--
--   $$\min_{Q\in O(k)}\Big(E_p\|\Phi_1(z)-Q\Phi_2(z)\|^2\Big)^{1/2}\le\frac{2\sqrt2}{\delta}\min\big(\sqrt k\,\|K_{\pi_1}-K_{\pi_2}\|_2,\ \|K_{\pi_1}-K_{\pi_2}\|_F\big).$$
--
--   When $k+1=|Z|$, $\delta=+\infty$ and the right side is $0$.
--
--   **Formalization Note** The minimum over $O(k)$ is stated as the existence of one $Q$ satisfying the bound. The case $k+1=|Z|$ is included, with right side $0$, as the convention $\mu_{|Z|}=-\infty$ of Proposition 1 gives.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c004; Section 2.2, Theorem 2, eq. (3), PDF pp. 3-4; proof in Appendix A.3, PDF p. 20

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem kernel_mismatch_bounds_misalignment {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (π₁ π₂ : Z → Z → ℝ) (h₁ : IsPairLaw p π₁) (h₂ : IsPairLaw p π₂)
    (hk : 1 ≤ k) (hkZ : k < Fintype.card Z)
    (hgap : k + 1 < Fintype.card Z → eigs p π₂ (k + 1) < eigs p π₂ k)
    (Phi₁ Phi₂ : Z → Fin k → ℝ) (hPhi₁ : IsSpectralEmbedding p π₁ Phi₁)
    (hPhi₂ : IsSpectralEmbedding p π₂ Phi₂) :
    ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ,
      l2Dist p Phi₁ (fun z => rot Q (Phi₂ z)) ≤ kahanBound p π₁ π₂ k := by sorry

end Arxiv2610_39302
