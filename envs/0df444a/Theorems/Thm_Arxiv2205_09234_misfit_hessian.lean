-- Prove2me | Theorems.Thm_Arxiv2205_09234_misfit_hessian
-- name    : Arxiv2205_09234.misfit_hessian
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T16:26:18.495848+00:00
-- url     : https://prove2.me/theorems/3c97199a-0012-54da-878f-b3113d62f663
-- title:
--   Eq. (4): Hessian of the $p=2$ metric with respect to $\mathbf d_m$ (as intended: conjugate transpose)
-- statement:
--   Let $N\ge1$, $\Delta t>0$, $\alpha\in\mathbb{R}$, let $\mathrm W_\alpha=\operatorname{diag}(w)$ be the weight matrix on the DFT sample frequencies, and fix $\mathbf d_o\in\mathbb{R}^N$. Then the matrix $\Omega^H\mathrm W_\alpha\Omega$ is real, and at every $\mathbf d_m\in\mathbb{R}^N$ the Hessian of $f(\mathbf d_m)=\mathcal L_{2,\alpha}(\mathbf d_m,\mathbf d_o)^2$ is the constant matrix
--
--   $$\nabla^2_{\mathbf d_m}\mathcal L_{2,\alpha}^2=2\,\Omega^{H}\mathrm W_\alpha\Omega.$$
--
--   This is the Hessian with respect to the data, not with respect to the subsurface model.
--
--   **Formalization Note** The Hessian is expressed as the derivative of the gradient map of $f$ on Euclidean $\mathbb{R}^N$. As for eq. (3), the paper's $\Omega^T$ is read as $\Omega^H$ and $\mathcal L_{2,\alpha}$ as its square.
-- source:
--   Izzatullah and Alkhalifah, omega-FWI: Robust full-waveform inversion with Fourier-based metric, arXiv:2205.09234v1 (2022), claim c005; Section 2.1, eq. (4), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

open MeasureTheory Matrix

namespace Arxiv2205_09234

theorem misfit_hessian (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt) (w : Fin N → ℝ)
    (hw : IsFreqWeight N dt α w) (dobs : Fin N → ℝ) :
    let A : Matrix (Fin N) (Fin N) ℂ := (dftMat N).conjTranspose * weightMat w * dftMat N
    (∀ i j, (A i j).im = 0) ∧
      ∀ x : EuclideanSpace ℝ (Fin N),
        HasFDerivAt
          (gradient fun y : EuclideanSpace ℝ (Fin N) =>
            discreteMetric N 2 w (fun j => y j) dobs ^ 2)
          (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (fun i j => 2 * (A i j).re)) x := by sorry

end Arxiv2205_09234
