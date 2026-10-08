-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_svm_zbar_shifted_soft_threshold
-- name    : BoydADMM.ModelFit.svm_zbar_shifted_soft_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:37:17.37831+00:00
-- url     : https://prove2.me/theorems/8ee113dd-83b8-4172-9d09-90475d407db7
-- title:
--   §8.3.4, pp. 70–71 — the feature-split SVM z̄-update is shifted soft thresholding of v = Ax̄^{k+1} + u^k
-- statement:
--   Let $N\ge1$, $\rho>0$, and $\overline{Ax},u\in\mathbb R^m$ (the averaged partial predictor $\overline{Ax}^{k+1}$ and the scaled dual variable $u^k$); write $v=\overline{Ax}+u$. The $\bar z$-update of the feature-split support vector machine minimizes
--   $$\mathbf 1^T(N\bar z+\mathbf 1)_++\frac{\rho}{2}\|\bar z-\overline{Ax}-u\|_2^2,$$
--   where $(w)_+$ is the componentwise positive part. A point $\bar z\in\mathbb R^m$ minimizes this function if and only if, for every component $j$,
--   $$\bar z_j=\begin{cases}v_j-N/\rho & v_j>-1/N+N/\rho\\ -1/N & v_j\in[-1/N,\,-1/N+N/\rho]\\ v_j & v_j<-1/N.\end{cases}$$
--   In particular the minimizer is unique.
--
--   The $\bar z$-update thus splits into $m$ scalar problems, each solved by this shifted soft thresholding.
--
--   **Formalization Note** The objective is exactly the one printed on p. 70, with coefficient $\rho/2$ on the quadratic; the general feature-split $\bar z$-update of p. 68 carries $N\rho/2$ instead, and the printed thresholds $N/\rho$ are the ones that match the printed $\rho/2$. The book writes $v=\overline{Ax}^{k+1}+\bar u^k$; after the reduction of §8.3 all duals are equal, so $\bar u^k=u^k$.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 70–71, §8.3.4

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.4, pp. 70–71: the feature-split SVM `z̄`-update
`argmin_{z̄} (1ᵀ(N z̄ + 1)₊ + (ρ/2)‖z̄ − Ax̄ − u‖₂²)` is the shifted soft thresholding of
`v = Ax̄ + u`, componentwise. -/
theorem svm_zbar_shifted_soft_threshold {N m : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Axbar u zb : EuclideanSpace ℝ (Fin m)) :
    IsMinOn (fun z : EuclideanSpace ℝ (Fin m) =>
        (∑ j, max ((N : ℝ) * z j + 1) 0) + ρ / 2 * ‖z - Axbar - u‖ ^ 2) Set.univ zb ↔
      ∀ j, zb j = shiftedSoftThreshold N ρ (Axbar j + u j) := by sorry

end BoydADMM.ModelFit
