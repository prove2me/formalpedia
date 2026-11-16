-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_lemma_31
-- name    : DistancePreserver934.Exact.Supplement.lemma_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:25:53.678473+00:00
-- url     : https://prove2.me/theorems/a326b82e-d492-41d2-ad6f-6455a955f3ff
-- title:
--   Lemma 31 — The parameterized +2 demand-removal construction
-- statement:
--   For one absolute $C>0$, every finite undirected unweighted graph $G$ with $n$ vertices, arbitrary ordered demand set $P$ of size $p$, and real parameters $d\ge\sqrt6$, $6\le r\le d^2$ admit an additive $+2$ spanner satisfying
--
--   $$|E(J)|\le C\left(pr+nd+\frac{np}{d^2\sqrt r}+\frac{p\sqrt{nr}}d\right).$$
--
--   All original demands and distances remain those of $G$, including trivial and unreachable pairs. The parameters and original $p$ stay fixed. This is an unconditional existence result for the full demand set, used by Theorem 27, with no $p\le n$ or private-length restriction.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Lemma 31, printed p. 28 (PDF p. 29)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem lemma_31 :

  ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : Finset (V × V)) (d r : ℝ),
    Real.sqrt 6 ≤ d → 6 ≤ r → r ≤ d ^ 2 →
    ∃ J : SimpleGraph V, IsAdditive G J P 2 ∧
      (numEdges J : ℝ) ≤ C * ((P.card : ℝ) * r + (Fintype.card V : ℝ) * d +
        (Fintype.card V : ℝ) * (P.card : ℝ) / (d ^ 2 * Real.sqrt r) +
        (P.card : ℝ) * Real.sqrt ((Fintype.card V : ℝ) * r) / d)
 := by sorry

end DistancePreserver934.Exact.Supplement
