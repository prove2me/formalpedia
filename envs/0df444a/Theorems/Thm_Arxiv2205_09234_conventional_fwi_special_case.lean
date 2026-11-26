-- Prove2me | Theorems.Thm_Arxiv2205_09234_conventional_fwi_special_case
-- name    : Arxiv2205_09234.conventional_fwi_special_case
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T16:14:24.641853+00:00
-- url     : https://prove2.me/theorems/d11d117c-063d-474c-8afe-12f43a4c4cb4
-- title:
--   Section 2.1 (before eq. (2)): conventional $\ell_2$ FWI is the case $p=2$, $\alpha=0$
-- statement:
--   Let $N\ge1$, $\Delta t>0$, and let $\mathrm W_0=\operatorname{diag}(w)$ be the weight matrix for $\alpha=0$. Then $\mathrm W_0=I$, and for all $\mathbf d_m,\mathbf d_o\in\mathbb{R}^N$
--
--   $$\mathcal L_{2,0}(\mathbf d_m,\mathbf d_o)^2=N\,\|\mathbf d_m-\mathbf d_o\|_2^2.$$
--
--   So for $p=2$, $\alpha=0$ the metric is the conventional sample-by-sample $\ell_2$ misfit of FWI, up to the constant factor $N$.
--
--   **Formalization Note** The paper does not say which parameters give conventional FWI; $p=2$, $\alpha=0$ is the reading under which the claim holds. The factor $N$ comes from the unnormalised DFT matrix.
-- source:
--   Izzatullah and Alkhalifah, omega-FWI: Robust full-waveform inversion with Fourier-based metric, arXiv:2205.09234v1 (2022), claim c003; Section 2.1, sentence introducing eq. (2), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

open MeasureTheory Matrix

namespace Arxiv2205_09234

theorem conventional_fwi_special_case (N : ℕ) (hN : 0 < N) (dt : ℝ) (hdt : 0 < dt)
    (w : Fin N → ℝ) (hw : IsFreqWeight N dt 0 w) (dm dobs : Fin N → ℝ) :
    (∀ k, w k = 1) ∧ discreteMetric N 2 w dm dobs ^ 2 = N * ∑ j, (dm j - dobs j) ^ 2 := by sorry

end Arxiv2205_09234
