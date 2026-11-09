-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_optimal_prediction_bound
-- name    : CaiZhuInfo.Matrix.optimal_prediction_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:17.251733+00:00
-- url     : https://prove2.me/theorems/d634cb67-6fc0-4bd5-9267-a6fc6ab9a045
-- title:
--   Theorem 5.1 — Optimal prediction bound
-- statement:
--   For arbitrary independent $X,Y\in F^m$, where $F$ is a finite field of size $q$ and $m\ge1$, define $\rho_{P_X}(y)=\frac{q\max_aP(X^\top y=a)-1}{q-1}$. Then
--   $$D(P_X\|U_{F^m})+D(P_Y\|U_{F^m})\ge m\log_2q\,\mathbb E_Y\rho_{P_X}(Y)-c_0.$$
--   The laws may have zero masses and need not be uniform. In particular $\rho_{P_X}(0)=1$. This quantifies the divergence required for optimal scalar prediction.
--
--   Differences from the source:
--   - encoding: independent random vectors over a finite field → arbitrary PMF marginals with their product law and Fin-indexed coordinates; reason: finite laws and independence are represented exactly; every finite field is allowed
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Theorem 5.1, (22),(23), printed p.15 / PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem optimal_prediction_bound {F : Type} [Field F] [Fintype F]
    (m : ℕ) (hm : 0 < m) (p q : PMF (Vec F m)) :
    (m : ℝ) * logTwo (Fintype.card F) * mean q (predictionAdvantage p) - c₀ ≤
      uniformDivergence p + uniformDivergence q := by sorry

end CaiZhuInfo.Matrix
