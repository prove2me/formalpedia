-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_lemma_5
-- name    : ChvatalOneHard398.SAT.Supplement.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:02.110094+00:00
-- url     : https://prove2.me/theorems/4c0b7182-3eba-47c8-a704-ad6f23df1c9d
-- title:
--   Lemma 5 — short dual basis
-- statement:
--   Let $B\in\mathbb R^{d\times d}$ be nonsingular and let $L=B\mathbb Z^d$. There is a basis $w_1,\ldots,w_d$ of the dual lattice such that
--   $$\|w_i\|_1\le\frac{d^2}{\lambda_1(L)}\quad\text{for every }i.$$
--
--   The basis and lattice are real, with no rationality or integrality restriction. The estimate provides the directions needed for thin parallelepipeds.
--
--   Differences from the source:
--   - encoding: Euclidean vectors and column lattice bases → Fin d coordinates and column-generated EuclideanSpace lattices; reason: the finite coordinates and Euclidean norm represent the same vectors and bases
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.11, Lemma 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem lemma_5 {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0) :
    ∃ W : Matrix (Fin d) (Fin d) ℝ, dualBasis (lattice B) W ∧
      ∀ i, oneNorm (fun j => W j i) ≤
        (d : ℝ)^2 / RegevLWE.SmoothingLB.lambda1 (lattice B) := by sorry

end ChvatalOneHard398.SAT.Supplement
