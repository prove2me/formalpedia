-- Prove2me | Theorems.Thm_Eliahou1993_farey_intermediate_coeffs
-- name    : Eliahou1993.farey_intermediate_coeffs
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:48.920561+00:00
-- url     : https://prove2.me/theorems/eae0e3dd-30f0-4c93-87a7-84b5dba8632a
-- title:
--   Eliahou (1993) Lemma 3.1 (linear form): positive integer Farey combination
-- statement:
--   Let $p, q, p', q', x, y \in \mathbb{N}$ be natural numbers with $q > 0$, $q' > 0$, and $y > 0$. Suppose that $p/q$ and $p'/q'$ form a Farey pair satisfying $p' q - p q' = 1$, and that the rational number $x / y$ lies strictly between them:
--
--   $$
--   \frac{p}{q} < \frac{x}{y} < \frac{p'}{q'} \implies \exists\, a, b \in \mathbb{N},\; a > 0 \;\wedge\; b > 0 \;\wedge\; x = a p + b p' \;\wedge\; y = a q + b q'.
--   $$
--
--   This structural refinement of the Farey mediant property expresses any rational fraction strictly inside a unimodular interval $(p/q, p'/q')$ as a positive integer linear combination of the endpoints, providing the exact integer coefficients needed for Eliahou's Theorem 1.1.
--
--   **Formalization Note** Stated in the `Eliahou1993` namespace (`Eliahou1993.farey_intermediate_coeffs`). This lemma is completely general and does not depend on any Collatz hypothesis. Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 49, Lemma 3.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/LinearForm.lean#L25-L73 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/LinearForm.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Lemma 3.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Cast.Order

theorem Eliahou1993.farey_intermediate_coeffs {p q p' q' x y : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hy : 0 < y)
    (hfarey : p' * q - p * q' = 1)
    (hleft : (p : ℚ) / q < x / y)
    (hright : (x : ℚ) / y < p' / q') :
    ∃ (a b : ℕ), 0 < a ∧ 0 < b ∧
      x = a * p + b * p' ∧ y = a * q + b * q' := by sorry
