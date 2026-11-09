-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_23
-- name    : ChvatalOneHard398.SAT.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:02.800375+00:00
-- url     : https://prove2.me/theorems/02965afb-80a0-4688-a3fb-036004524ed8
-- title:
--   Lemma 23 — nearby dual lattice vectors
-- statement:
--   Let $M=B\mathbb Z^m\subseteq\mathbb R^m$ for an arbitrary nonsingular real matrix $B$, and let $y\in\mathbb R^m$. Then
--
--   $$\exists w\in M^*:\quad\sum_{i=1}^m|w_i-y_i|\le\frac{m^{3/2}}{2\lambda_1(M)}.$$
--
--   This is the stated bound in the coordinate one-norm. It supplies the dual approximation estimate used in the thin-formula rank condition.
--
--   Differences from the source:
--   - encoding: real coordinate vectors, integer points, and lattice notation → Fin-indexed real coordinates, explicit integer-point predicates, and Euclidean integer column spans; reason: these represent the same vectors and full-rank lattices; norms on lattices are Euclidean
--   - encoding: an arbitrary full-rank lattice and the ℓ₁ norm → a nonsingular real column matrix and an explicit sum of coordinate absolute values; reason: every source lattice has such a basis and every such basis generates a source lattice; this avoids confusing coordinate sup norm with Euclidean norm
--   - generalization: the shortest-nonzero-vector bound in positive dimension → the same bound also at m=0 using the total real infimum and division conventions; reason: every source instance is retained; at m=0 the unique vectors have zero coordinate sum, lambda1 is 0 and the bound reduces to 0≤0
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.24, Lemma 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Geometry

namespace ChvatalOneHard398.SAT
open scoped BigOperators

theorem lemma_23 {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.det ≠ 0)
    (y : E m) :
    ∃ w ∈ RegevLWE.GaussConv.dual (lattice B),
      ∑ i, |w i-y i| ≤ (m : ℝ)^(3/2 : ℝ)/(2*RegevLWE.SmoothingLB.lambda1 (lattice B)) := by sorry

end ChvatalOneHard398.SAT
