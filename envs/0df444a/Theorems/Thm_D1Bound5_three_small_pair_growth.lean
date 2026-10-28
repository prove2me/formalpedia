-- Prove2me | Theorems.Thm_D1Bound5_three_small_pair_growth
-- name    : D1Bound5.three_small_pair_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:46.033819+00:00
-- url     : https://prove2.me/theorems/b3f0240f-ffae-40ab-a8c2-fc488fe7e509
-- title:
--   Both alternatives imply quadratic growth of a large pair
-- statement:
--   Let $P,Q$ be real numbers with $P\ge1000$. If
--   $$\bigl(5P^2<Q<405P^2\bigr)\quad\text{or}\quad \frac{P^5}{400}<Q,$$
--   then
--   $$5P^2<Q.$$
--   This extracts the common growth bound from the pair alternatives.
-- source:
--   D1Bound5/ThreeSmallPairAlternative.lean, D1Bound5.three_small_pair_growth, lines 72-81; original file SHA-256 3dc02360d7110c7469529da785f83b480f3aecc6182b6bb58ab6b87d9082a50e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.three_small_pair_growth (P Q : ℝ) (hP : 1000 ≤ P)
    (halt : (5*P^2 < Q ∧ Q < 405*P^2) ∨ P^5/400 < Q) : 5*P^2 < Q := by sorry
