-- Prove2me | Theorems.Thm_Arxiv2205_09234_misfit_gradient
-- name    : Arxiv2205_09234.misfit_gradient
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T16:20:56.838566+00:00
-- url     : https://prove2.me/theorems/f85a3955-92ff-5538-9026-815f794696f4
-- title:
--   Eq. (3): gradient of the $p=2$ metric with respect to $\mathbf d_m$ (as intended: conjugate transpose)
-- statement:
--   Let $N\ge1$, $\Delta t>0$, $\alpha\in\mathbb{R}$, let $\mathrm W_\alpha=\operatorname{diag}(w)$ be the weight matrix on the DFT sample frequencies, and fix $\mathbf d_o\in\mathbb{R}^N$. Consider $f(\mathbf d_m)=\mathcal L_{2,\alpha}(\mathbf d_m,\mathbf d_o)^2$ as a function on Euclidean $\mathbb{R}^N$. Then for every $\mathbf d_m$ the vector $\Omega^H\mathrm W_\alpha\Omega(\mathbf d_m-\mathbf d_o)$ is real, and
--
--   $$\nabla_{\mathbf d_m}\mathcal L_{2,\alpha}^2=2\,\Omega^{H}\mathrm W_\alpha\Omega\,(\mathbf d_m-\mathbf d_o).$$
--
--   Half of this vector, $\Omega^H\mathrm W_\alpha\Omega(\mathbf d_m-\mathbf d_o)$, is the adjoint source of the misfit $J=\tfrac12\mathcal L_{2,\alpha}^2$ of eq. (5).
--
--   **Formalization Note** The paper prints $2\Omega^T\mathrm W_\alpha\Omega(\mathbf d_m-\mathbf d_o)$ as the gradient of $\mathcal L_{2,\alpha}$. That is the gradient of the printed plain-transpose form of eq. (2). It is not the gradient of the metric: for $\alpha=0$ it equals $2N$ times the index-reversed residual. The statement is for the square of the metric, with the conjugate transpose, consistently with the statement of eq. (2).
-- source:
--   Izzatullah and Alkhalifah, omega-FWI: Robust full-waveform inversion with Fourier-based metric, arXiv:2205.09234v1 (2022), claim c004; Section 2.1, eq. (3), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

open MeasureTheory Matrix

namespace Arxiv2205_09234

theorem misfit_gradient (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt) (w : Fin N → ℝ)
    (hw : IsFreqWeight N dt α w) (dobs : Fin N → ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    let A : Matrix (Fin N) (Fin N) ℂ := (dftMat N).conjTranspose * weightMat w * dftMat N
    let r : Fin N → ℂ := fun j => ((x j - dobs j : ℝ) : ℂ)
    (∀ j, (A.mulVec r j).im = 0) ∧
      HasGradientAt
        (fun y : EuclideanSpace ℝ (Fin N) => discreteMetric N 2 w (fun j => y j) dobs ^ 2)
        (WithLp.toLp 2 (fun j => 2 * (A.mulVec r j).re)) x := by sorry

end Arxiv2205_09234
