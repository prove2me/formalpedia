-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_exact_prediction
-- name    : CaiZhuInfo.Matrix.exact_prediction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:36.17581+00:00
-- url     : https://prove2.me/theorems/f755746c-e5d7-4cea-87e7-a8b5675f537b
-- title:
--   Lemma 5.4 — Exact inner-product prediction
-- statement:
--   Let $X,Y\in F^m$ have arbitrary independent laws over a finite field of size $q$, with $m\ge1$. If a decoder $z:F^m\to F$ predicts $X^\top Y$ with probability one, then
--   $$D(P_X\|U_{F^m})+D(P_Y\|U_{F^m})\ge m\log_2q.$$
--   The zero-error constraint is expressed as the actual error probability being zero. No support-subspace restriction is assumed, and there is no additive constant loss. This supplies the exact zero-error branch.
--
--   Differences from the source:
--   - encoding: independent random vectors over a finite field → arbitrary PMF marginals with their product law and Fin-indexed coordinates; reason: finite laws and independence are represented exactly; every finite field is allowed
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma 5.4, (32), printed p.18 / PDF p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem exact_prediction {F : Type} [Field F] [Fintype F]
    (m : ℕ) (hm : 0 < m) (p q : PMF (Vec F m)) (z : Vec F m → F)
    (hz : predictionError p q innerProduct z = 0) :
    (m : ℝ) * logTwo (Fintype.card F) ≤
      uniformDivergence p + uniformDivergence q := by sorry

end CaiZhuInfo.Matrix
