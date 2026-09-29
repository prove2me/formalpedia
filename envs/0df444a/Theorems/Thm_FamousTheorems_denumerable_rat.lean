-- Prove2me | Theorems.Thm_FamousTheorems_denumerable_rat
-- name    : FamousTheorems.denumerable_rat
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:17:15.122657+00:00
-- url     : https://prove2.me/theorems/c8caeae7-9180-4db5-ae44-94bdfd707431
-- title:
--   The denumerability of the rational numbers
-- statement:
--   **The rationals are countable.**
--
--   There is a bijection $\mathbb{N} \leftrightarrow \mathbb{Q}$.
--
--   Cantor's 1874 result, and a genuine surprise: $\mathbb{Q}$ is dense in $\mathbb{R}$ — between
--   any two rationals lies another — yet it has exactly as many elements as the sparse, discrete
--   $\mathbb{N}$. Density and cardinality are unrelated.
--
--   The standard enumeration lists the fractions in a grid by anti-diagonals, skipping
--   non-reduced entries; the Stern–Brocot tree and the Calkin–Wilf sequence give explicit
--   bijections with no skipping at all.
--
--   Paired with the uncountability of $\mathbb{R}$, this is what shows the irrationals — indeed the
--   transcendentals — form the overwhelming majority of the reals.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem denumerable_rat : Nonempty (ℕ ≃ ℚ) := by sorry

end FamousTheorems
