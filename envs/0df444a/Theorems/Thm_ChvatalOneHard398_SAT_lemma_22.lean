-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_22
-- name    : ChvatalOneHard398.SAT.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:45.404501+00:00
-- url     : https://prove2.me/theorems/09db4758-bb0a-4e16-b1d2-0c8f73c4698e
-- title:
--   Lemma 22 — dual of the congruence lattice
-- statement:
--   Let $D,m,m'\ge1$ and let $H\in\mathbb Z^{m'\times m}$ be arbitrary. For $M=\{y\in\mathbb Z^m:Hy\equiv0\pmod D\}$,
--
--   $$DM^*=H^T\mathbb Z^{m'}+D\mathbb Z^m.$$
--
--   The equality is between sets in Euclidean space, and the right side is expressed through its two integer coefficient vectors. This describes every scaled dual vector without requiring $H$ to be reduced modulo $D$.
--
--   Differences from the source:
--   - encoding: real coordinate vectors, integer points, and lattice notation → Fin-indexed real coordinates, explicit integer-point predicates, and Euclidean integer column spans; reason: these represent the same vectors and full-rank lattices; norms on lattices are Euclidean
--   - encoding: the sum Hᵀℤᵐ′+Dℤᵐ → the set of all Hᵀz+Du with integer z,u; reason: existential integer coefficient vectors express exactly this Minkowski sum
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.24, Lemma 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Geometry

namespace ChvatalOneHard398.SAT
open scoped BigOperators

theorem lemma_22 {m r : ℕ} (D : ℕ) (hD : 1 ≤ D) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (H : Matrix (Fin r) (Fin m) ℤ) :
    (fun w : E m => (D : ℝ) • w) ''
        (RegevLWE.GaussConv.dual (congruenceLattice D H) : Set (E m)) =
      {y : E m | ∃ (z : Fin r → ℤ) (u : Fin m → ℤ),
        y = WithLp.toLp 2 (fun j => (((∑ i, H i j * z i) + (D : ℤ)*u j : ℤ) : ℝ))} := by sorry

end ChvatalOneHard398.SAT
