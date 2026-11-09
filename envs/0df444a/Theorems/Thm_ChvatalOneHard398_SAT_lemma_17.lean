-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_17
-- name    : ChvatalOneHard398.SAT.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:48.426783+00:00
-- url     : https://prove2.me/theorems/b762f7ed-400c-4fed-92f3-e90e570dbc25
-- title:
--   Lemma 17 — integral affine lifts
-- statement:
--   Let $P\subseteq\mathbb R^N$ be a rational polyhedron, $A\in\mathbb Z^{N'\times N}$, and $b\in\mathbb Z^{N'}$. For $\phi(x)=(x,Ax+b)$,
--
--   $$\phi:P\cap\mathbb Z^N\longrightarrow\phi(P)\cap\mathbb Z^{N+N'}\text{ is bijective},\qquad\phi(P)_I=\phi(P_I),\qquad\phi(P)'=\phi(P').$$
--
--   This permits the introduction of integral affine auxiliary variables while preserving integer points, integer hulls, and the first closure.
--
--   Differences from the source:
--   - encoding: real coordinate vectors, integer points, and lattice notation → Fin-indexed real coordinates, explicit integer-point predicates, and Euclidean integer column spans; reason: these represent the same vectors and full-rank lattices; norms on lattices are Euclidean
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.18, Lemma 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Geometry

namespace ChvatalOneHard398.SAT
open CombOpt.ChvatalRank

theorem lemma_17 {n k : ℕ} (P : Set (Fin n → ℝ)) (hP : IsRationalPolyhedron P)
    (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ) :
    Set.BijOn (affineLift A b) {x | x ∈ P ∧ IsIntegralVector x}
      {y | y ∈ affineLift A b '' P ∧ IsIntegralVector y} ∧
    integerHull (affineLift A b '' P) = affineLift A b '' integerHull P ∧
    chvatalClosure (affineLift A b '' P) = affineLift A b '' chvatalClosure P := by sorry

end ChvatalOneHard398.SAT
