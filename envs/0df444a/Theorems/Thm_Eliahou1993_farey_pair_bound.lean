-- Prove2me | Theorems.Thm_Eliahou1993_farey_pair_bound
-- name    : Eliahou1993.farey_pair_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:47.668214+00:00
-- url     : https://prove2.me/theorems/aa9ed748-eeb3-4fa0-af72-37684ab690c1
-- title:
--   Eliahou (1993) Lemma 3.1: mediant lower bound for fractions between a Farey pair
-- statement:
--   Let $p, q, p', q', x, y \in \mathbb{N}$ be natural numbers with $q > 0$, $q' > 0$, and $y > 0$. Suppose that $p/q$ and $p'/q'$ form a Farey pair in the sense that $p' q - p q' = 1$, and that the rational fraction $x / y$ lies strictly between them:
--
--   $$
--   \frac{p}{q} < \frac{x}{y} < \frac{p'}{q'} \implies p + p' \le x \quad \text{and} \quad q + q' \le y.
--   $$
--
--   This general diophantine approximation property (Eliahou 1993, Lemma 3.1) requires no cycle-specific assumptions and provides lower bounds on the numerator and denominator of any rational number trapped inside a Farey interval.
--
--   **Formalization Note** Stated in the `Eliahou1993` namespace (`Eliahou1993.farey_pair_bound`) using natural-number subtraction `p' * q - p * q' = 1` and rational inequalities `(p : ℚ) / q < x / y` and `(x : ℚ) / y < p' / q'`. Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 49, Lemma 3.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/ContinuedFractions.lean#L45-L55 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/ContinuedFractions.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Lemma 3.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Cast.Order

theorem Eliahou1993.farey_pair_bound {p q p' q' x y : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hy : 0 < y)
    (hfarey : p' * q - p * q' = 1)
    (hleft : (p : ℚ) / q < x / y)
    (hright : (x : ℚ) / y < p' / q') :
    p + p' ≤ x ∧ q + q' ≤ y := by sorry
