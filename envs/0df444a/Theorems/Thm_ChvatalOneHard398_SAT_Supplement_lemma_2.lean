-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_lemma_2
-- name    : ChvatalOneHard398.SAT.Supplement.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:21:22.727277+00:00
-- url     : https://prove2.me/theorems/45855a1f-91e6-45c4-be41-eec5e2f8c051
-- title:
--   Lemma 2 — unimodular widths
-- statement:
--   Let $P\subseteq\mathbb R^d$ be a rational polyhedron and let $U$ be a unimodular integer matrix with rows $u_i^T$. Assume $\operatorname{width}_P(u_i)<1$ for every row. Then
--   $$P'=P_I,$$
--   and $P_I$ is the intersection of $P$ with at most $2d$ CG cuts. Moreover $P$ contains at most one integral vector, and every rational subpolyhedron of $P$ has Chvátal rank at most one.
--
--   This is the width criterion used for the parallelepiped hardness result. The empty polyhedron is included, with a cut family of size zero sufficient for its hull.
--
--   Differences from the source:
--   - encoding: Euclidean vectors and column lattice bases → Fin d coordinates and column-generated EuclideanSpace lattices; reason: the finite coordinates and Euclidean norm represent the same vectors and bases
--   - encoding: support-function widths, with empty sets handled separately → EReal support values for nonempty sets and width zero for the empty set; reason: unbounded widths stay infinite and every empty-set conclusion is retained
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.10, Lemma 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem lemma_2 {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ)
    (P : Set (Fin d → ℝ)) (hU : unimodular U) (hP : IsRationalPolyhedron P)
    (hw : ∀ i, width P (fun j => (U i j : ℝ)) < 1) :
    rankOne P ∧
    (∃ k : ℕ, k ≤ 2*d ∧ ∃ (c : Fin k → Fin d → ℝ) (t : Fin k → ℝ),
      (∀ i, IsGomoryChvatalCut P (c i) (t i)) ∧
      integerHull P = {x | x ∈ P ∧ ∀ i, ∑ j, c i j*x j ≤ t i}) ∧
    Subsingleton (integralPoints P) ∧ hereditaryRankOne P := by sorry

end ChvatalOneHard398.SAT.Supplement
