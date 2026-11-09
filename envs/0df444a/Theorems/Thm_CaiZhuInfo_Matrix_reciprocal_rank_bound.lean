-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_reciprocal_rank_bound
-- name    : CaiZhuInfo.Matrix.reciprocal_rank_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:01.714723+00:00
-- url     : https://prove2.me/theorems/da23b7bb-f0ed-47fb-b7f6-aca738fec4bf
-- title:
--   Lemma 6.3 — Reciprocal-rank bound
-- statement:
--   For every finite field $F$ and integers $1\le t\le s$, let $\Lambda$ be uniform on all nonzero $t\times s$ matrices. Then
--   $$\kappa_{q,t,s}=\mathbb E_\Lambda\frac t{\operatorname{rank}\Lambda}\le2.$$
--   The average includes nonzero singular matrices. This uniform bound supplies the dimension-independent additive gap in the main theorem.
--
--   Differences from the source:
--   - encoding: a uniform nonzero matrix over F_q → the finite average of t divided by the actual rank over all nonzero matrices over an arbitrary finite field; reason: the cardinality of the carrier is q, including nonprime prime powers
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma 6.3, (36), printed p.21 / PDF p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem reciprocal_rank_bound {F : Type} [Field F] [Fintype F]
    (t s : ℕ) (ht : 0 < t) (hts : t ≤ s) : kappa F t s ≤ 2 := by sorry

end CaiZhuInfo.Matrix
