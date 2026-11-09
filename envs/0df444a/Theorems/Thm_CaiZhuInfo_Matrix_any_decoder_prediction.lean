-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_any_decoder_prediction
-- name    : CaiZhuInfo.Matrix.any_decoder_prediction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:01.05904+00:00
-- url     : https://prove2.me/theorems/79470e83-3bf3-4512-a665-1e9c5020a218
-- title:
--   Corollary 5.3 — Prediction bound for any decoder
-- statement:
--   Let $X,Y\in F^m$ be arbitrary independent vectors over a finite field of size $q$, with $m\ge1$. For any deterministic decoder $z:F^m\to F$, set $\eta=P(z(Y)\ne X^\top Y)$. Then
--   $$D(P_X\|U_{F^m})+D(P_Y\|U_{F^m})\ge m\log_2q\left(1-\frac q{q-1}\eta\right)-c_0.$$
--   There is no optimality requirement and no restriction of $\eta$ to errors below uniform guessing. This form applies to the decoder induced by a protocol transcript.
--
--   Differences from the source:
--   - encoding: independent random vectors over a finite field → arbitrary PMF marginals with their product law and Fin-indexed coordinates; reason: finite laws and independence are represented exactly; every finite field is allowed
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Corollary 5.3, (31), printed p.18 / PDF p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem any_decoder_prediction {F : Type} [Field F] [Fintype F]
    (m : ℕ) (hm : 0 < m) (p q : PMF (Vec F m)) (z : Vec F m → F) :
    (m : ℝ) * logTwo (Fintype.card F) *
      (1 - (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) - 1) *
        predictionError p q innerProduct z) - c₀ ≤
      uniformDivergence p + uniformDivergence q := by sorry

end CaiZhuInfo.Matrix
