-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_optimal_prediction_moment
-- name    : CaiZhuInfo.Matrix.optimal_prediction_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:55.196788+00:00
-- url     : https://prove2.me/theorems/85335a1d-9e4f-4924-9f64-9bd2be35152d
-- title:
--   Lemma 5.2 — Exponential moment of an optimal prediction rule
-- statement:
--   Let $F$ be a finite field of size $q$, $m\ge1$, and let $X,Y\in V=F^m$ have arbitrary independent laws. There exists $\phi:V\to F$ that maximizes $P(X^\top y=a)$ for every $y$, and, with $f_\phi(x)=1-\frac q{q-1}P_Y(x^\top Y\ne\phi(Y))$, satisfies
--   $$\log_2\mathbb E_{U\sim U_V}2^{m\log_2q\,f_\phi(U)}\le D(P_Y\|U_V)+c_0.$$
--   The exponential moment and optimality are conclusions. No homogeneity condition on a supplied rule is assumed. This is the full moment estimate used by the optimal prediction theorem.
--
--   Differences from the source:
--   - encoding: independent random vectors over a finite field → arbitrary PMF marginals with their product law and Fin-indexed coordinates; reason: finite laws and independence are represented exactly; every finite field is allowed
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma 5.2, (24),(27), printed p.16 / PDF p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem optimal_prediction_moment {F : Type} [Field F] [Fintype F]
    (m : ℕ) (hm : 0 < m) (p q : PMF (Vec F m)) :
    ∃ φ : Vec F m → F, OptimalPredictor p φ ∧
      logTwo (mean (uniformLaw (Vec F m)) (fun u =>
        (2 : ℝ) ^ ((m : ℝ) * logTwo (Fintype.card F) * predictionScore q φ u))) ≤
      uniformDivergence q + c₀ := by sorry

end CaiZhuInfo.Matrix
