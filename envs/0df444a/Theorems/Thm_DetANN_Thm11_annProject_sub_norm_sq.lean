-- Prove2me | Theorems.Thm_DetANN_Thm11_annProject_sub_norm_sq
-- name    : DetANN.Thm11.annProject_sub_norm_sq
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:44.696049+00:00
-- url     : https://prove2.me/theorems/6c83c416-a3fd-4072-9aa7-0fd4478ef7e7
-- title:
--   The vector superblock has the squared norm used in equation (25)
-- statement:
--   Let $\mathcal A_v$ be the vector-valued superblock projection for a walk tuple $v$, with dimension $16^\ell L$ and occurrence-major coordinates. For every $z,w\in\mathbb R^{2^k}$,
--   $$
--   \|\mathcal A_v(z-w)\|_2^2
--    =\sum_{o}\|A_{S_v(o)}(z-w)\|_2^2.
--   $$
--   The sum ranges over all $16^\ell$ walk occurrences, retaining multiplicities, and the right-hand side is `superNormSq`. Thus the ordinary Euclidean distances used by the local Lemma 3.3 structures are exactly the superblock distances in the local guarantee (25). The statement requires no nondegeneracy hypotheses.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §7.1, p.17, definition of $\mathcal A_v$ and equation (25).

import Mathlib
import Definitions.Def_DetANN_Thm11_LocalProjection

/-- The squared norm of a projected difference is the superblock squared norm of that difference. -/
theorem DetANN.Thm11.annProject_sub_norm_sq {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (z w : EuclideanSpace ℝ (Fin (2 ^ k))) :
    ‖annProject C₀ k P ε v (z - w)‖ ^ 2 =
      superNormSq (annBlocks C₀ k P ε) (annTuples k ε) v (z - w) := by sorry
