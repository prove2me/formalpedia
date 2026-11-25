-- Prove2me | Theorems.Thm_Arxiv2205_09234_weighted_l2_form
-- name    : Arxiv2205_09234.weighted_l2_form
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T16:07:04.730355+00:00
-- url     : https://prove2.me/theorems/2a655d72-0fff-44fa-ac9a-2414c7f31cbc
-- title:
--   Eq. (2): the $p=2$ Fourier-based metric is a weighted $\ell_2$ norm (as intended: squared, conjugate transpose)
-- statement:
--   Let $N\ge1$, $\Delta t>0$, $\alpha\in\mathbb{R}$, let $\mathrm W_\alpha=\operatorname{diag}(w)$ be the weight matrix on the DFT sample frequencies, and let $\mathbf d_m,\mathbf d_o\in\mathbb{R}^N$ with $\hat{\mathbf d}=\Omega\mathbf d$. Then the discrete Fourier-based metric with $p=2$ is a weighted $\ell_2$ norm:
--
--   $$\mathcal L_{2,\alpha}(\mathbf d_m,\mathbf d_o)^2=(\hat{\mathbf d}_m-\hat{\mathbf d}_o)^{H}\,\mathrm W_\alpha\,(\hat{\mathbf d}_m-\hat{\mathbf d}_o)=(\mathbf d_m-\mathbf d_o)^{T}\,\Omega^{H}\mathrm W_\alpha\Omega\,(\mathbf d_m-\mathbf d_o).$$
--
--   This is the paper's reformulation of the metric as a weighted $\ell_2$ misfit.
--
--   **Formalization Note** The paper prints $\mathcal L_{2,\alpha}$ (not its square) on the left and the plain transpose $^T$ of the complex vector $\hat{\mathbf d}_m-\hat{\mathbf d}_o$. The printed left side is the square root of the right side, and with $^T$ the right side can be negative, so it is not the metric. The statement uses the square and the conjugate transpose $^H$, which is what the identity establishes.
-- source:
--   Izzatullah and Alkhalifah, omega-FWI: Robust full-waveform inversion with Fourier-based metric, arXiv:2205.09234v1 (2022), claim c012; Section 2.1, eq. (2), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

open MeasureTheory Matrix

namespace Arxiv2205_09234

theorem weighted_l2_form (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt) (w : Fin N → ℝ)
    (hw : IsFreqWeight N dt α w) (dm dobs : Fin N → ℝ) :
    let rhat : Fin N → ℂ := fun k => dft N dm k - dft N dobs k
    let r : Fin N → ℂ := fun j => ((dm j - dobs j : ℝ) : ℂ)
    ((discreteMetric N 2 w dm dobs ^ 2 : ℝ) : ℂ) = star rhat ⬝ᵥ (weightMat w).mulVec rhat ∧
      star rhat ⬝ᵥ (weightMat w).mulVec rhat =
        r ⬝ᵥ ((dftMat N).conjTranspose * weightMat w * dftMat N).mulVec r := by sorry

end Arxiv2205_09234
