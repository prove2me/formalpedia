-- Prove2me | Theorems.Thm_Eliahou1993_eliahou_product_formula
-- name    : Eliahou1993.eliahou_product_formula
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:52.319171+00:00
-- url     : https://prove2.me/theorems/01bd99c7-09d9-4f17-b370-7f69e3ce279c
-- title:
--   Eliahou (1993) Lemma 2.2: integer product identity for Collatz cycles
-- statement:
--   Let $(x_0, x_1, \dots, x_{L-1})$ be a cycle of length $L > 0$ of the compressed Collatz map $T(n) = n/2$ (for $n$ even) and $T(n) = (3n+1)/2$ (for $n$ odd), with $x_i > 0$ and $T(x_i) = x_{(i+1) \bmod L}$ for all $i \in \{0, \dots, L-1\}$. Let $\Omega_1 = \{i : x_i \equiv 1 \pmod 2\}$ denote the set of indices of odd elements in the cycle. Then
--
--   $$
--   \prod_{i \in \Omega_1} (3x_i + 1) = 2^L \prod_{i \in \Omega_1} x_i.
--   $$
--
--   This unconditional algebraic identity (Eliahou 1993, Lemma 2.2) holds for every positive compressed Collatz cycle without any lower-bound hypothesis on the cycle minimum, and forms the starting point for deriving multiplicative and logarithmic bounds on the ratio $L / |\Omega_1|$.
--
--   **Formalization Note** Stated in the `Eliahou1993` namespace for any `c : Eliahou1993.CollatzCycle L`. Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 48, Lemma 2.2; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/ProductFormula.lean#L109-L120 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/ProductFormula.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Lemma 2.2.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Definitions.Def_eliahou1993Cycle

open Finset BigOperators Eliahou1993

theorem Eliahou1993.eliahou_product_formula {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 * c.seq i + 1) =
    2 ^ L * ∏ i ∈ c.oddIndices, c.seq i := by sorry
