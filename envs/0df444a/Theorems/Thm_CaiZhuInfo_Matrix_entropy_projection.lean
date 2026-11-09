-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_entropy_projection
-- name    : CaiZhuInfo.Matrix.entropy_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:13.812107+00:00
-- url     : https://prove2.me/theorems/8a50e597-5d4f-4dd0-a461-0a446957b307
-- title:
--   Theorem 6.2 — Rank-normalized entropy projection
-- statement:
--   Let $Z$ have any law on $F^{t\times m}$ and choose $T$ independently and uniformly from all full-row-rank matrices in $F^{d\times t}$, where $1\le d\le t$. Then both inequalities hold:
--   $$H(TZ\mid T)\ge\frac dt H(Z),\qquad\mathbb E_TD(P_{TZ\mid T}\|U_{F^{d\times m}})\le\frac dtD(P_Z\|U_{F^{t\times m}}).$$
--   No rank, uniformity or full-support assumption is placed on $Z$. These control the entropy and divergence of an independent uniform projection without accumulating a loss per row.
--
--   Differences from the source:
--   - encoding: an independent uniform full-row-rank projection T and conditional law of TZ → the finite average over every full-row-rank T of the pushforward of the given law of Z; reason: independence makes this pushforward the conditional law given T; both entropy and divergence clauses are retained
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Theorem 6.2, (34)–(35), printed p.20 / PDF p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem entropy_projection {F : Type} [Field F] [Fintype F]
    (d t m : ℕ) (hd : 0 < d) (hdt : d ≤ t) (p : PMF (Mat F t m)) :
    ((d : ℝ) / t) * finiteEntropy p ≤
      projectionMean (fun T : Mat F d t => finiteEntropy (projectedLaw T p)) ∧
    projectionMean (fun T : Mat F d t => uniformDivergence (projectedLaw T p)) ≤
      ((d : ℝ) / t) * uniformDivergence p := by sorry

end CaiZhuInfo.Matrix
