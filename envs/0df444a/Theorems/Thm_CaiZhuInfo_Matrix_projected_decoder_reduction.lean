-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_projected_decoder_reduction
-- name    : CaiZhuInfo.Matrix.projected_decoder_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:13.044827+00:00
-- url     : https://prove2.me/theorems/6c1c8df1-0b1c-4e29-a8c6-22f4f6eb41d7
-- title:
--   Projected decoding — unnumbered reduction in Appendix D.2 and (39)
-- statement:
--   Let $L\in F^{d\times t}$ and $R\in F^{d\times s}$ have full row rank, with $d,m\ge1$, and let $X\in F^{t\times m}$ and $Y\in F^{s\times m}$ have arbitrary independent laws. Let $z(Y)$ predict the entrywise product $\langle LX,RY\rangle_F$, with error $\eta$. Write $P'$ and $Q'$ for the actual laws of $LX$ and $RY$. There exists a decoder $z'(RY)$ with error at most $\eta$. Moreover,
--   $$D(P'\|U_{F^{d\times m}})+D(Q'\|U_{F^{d\times m}})\ge dm\log_2q\left(1-\frac q{q-1}\eta\right)-c_0.$$
--   When $\eta=0$ the lower bound improves to $dm\log_2q$. These are bounds on the projected divergences, retaining Bob's original decoder access to all of $Y$. This is an unnumbered supporting item and is not a numbered milestone.
--
--   Differences from the source:
--   - encoding: the projected vector inputs in Appendix D.2 and the matrices viewed as vectors in (39) → actual pushforward laws of LX and RY on Fin-indexed arrays, with Frobenius inner product; reason: flattening d by m coordinates is a bijection with the source vector space of dimension dm
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Appendix D.2 proof of Lemma D.1 and §6.3 (39), also PDF p.34 / printed p.33, printed p.22 / PDF p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem projected_decoder_reduction {F : Type} [Field F] [Fintype F]
    {d t s m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (L : Mat F d t) (R : Mat F d s) (hL : L.rank = d) (hR : R.rank = d)
    (p : PMF (Mat F t m)) (q : PMF (Mat F s m)) (z : Mat F s m → F) :
    let p' := projectedLaw L p
    let q' := projectedLaw R q
    let η := predictionError p q (fun X Y => frobenius (L * X) (R * Y)) z
    (∃ z' : Mat F d m → F, predictionError p' q' frobenius z' ≤ η) ∧
    ((d : ℝ) * m * logTwo (Fintype.card F) *
      (1 - (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) - 1) * η) - c₀ ≤
        uniformDivergence p' + uniformDivergence q') ∧
    (η = 0 → (d : ℝ) * m * logTwo (Fintype.card F) ≤
      uniformDivergence p' + uniformDivergence q') := by sorry

end CaiZhuInfo.Matrix
