-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_bilinear_prediction
-- name    : CaiZhuInfo.Matrix.bilinear_prediction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:25.111363+00:00
-- url     : https://prove2.me/theorems/81397439-fe3f-4e91-975f-5bc29692da54
-- title:
--   Lemma D.1 — Bilinear prediction
-- statement:
--   Let $A\in F^{n\times m}$ have rank $r\ge1$, where $F$ is a finite field of size $q$. For arbitrary independent laws of $X\in F^n$ and $Y\in F^m$, and any decoder $z:F^m\to F$, put $\eta=P(z(Y)\ne X^\top AY)$. Then
--   $$D(P_X\|U_{F^n})+D(P_Y\|U_{F^m})\ge r\log_2q\left(1-\frac q{q-1}\eta\right)-c_0.$$
--   If $\eta=0$, the stronger bound is
--   $$D(P_X\|U_{F^n})+D(P_Y\|U_{F^m})\ge r\log_2q.$$
--   Both conclusions are included. The separate unnumbered projected-decoder item records the proof's stronger intermediate conclusion needed in the matrix argument.
--
--   Differences from the source:
--   - encoding: independent random vectors over a finite field → arbitrary PMF marginals with their product law and Fin-indexed coordinates; reason: finite laws and independence are represented exactly; every finite field is allowed
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma D.1, (59)–(60), printed p.32 / PDF p.33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem bilinear_prediction {F : Type} [Field F] [Fintype F]
    {n m : ℕ} (A : Mat F n m) (hr : 0 < A.rank)
    (p : PMF (Vec F n)) (q : PMF (Vec F m)) (z : Vec F m → F) :
    let η := predictionError p q (bilinearForm A) z
    ((A.rank : ℝ) * logTwo (Fintype.card F) *
      (1 - (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) - 1) * η) - c₀ ≤
        uniformDivergence p + uniformDivergence q) ∧
    (η = 0 → (A.rank : ℝ) * logTwo (Fintype.card F) ≤
      uniformDivergence p + uniformDivergence q) := by sorry

end CaiZhuInfo.Matrix
