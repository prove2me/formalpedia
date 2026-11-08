-- Prove2me | Theorems.Thm_Eliahou1993_eliahou_product_formula_real
-- name    : Eliahou1993.eliahou_product_formula_real
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:57.400175+00:00
-- url     : https://prove2.me/theorems/3767661d-8ee7-474b-afb3-904de245f09f
-- title:
--   Eliahou (1993) Lemma 2.2 (real form): rational-factor product formula for Collatz cycles
-- statement:
--   Let $c = (x_0, x_1, \dots, x_{L-1})$ be a positive cycle of length $L > 0$ of the compressed Collatz map $T$, and let $\Omega_1 = \{i \in \{0, \dots, L-1\} : x_i \equiv 1 \pmod 2\}$ denote the set of indices of odd cycle elements. Viewed in the real numbers $\mathbb{R}$, the cycle satisfies
--
--   $$
--   \prod_{i \in \Omega_1} \left(3 + \frac{1}{x_i}\right) = 2^L.
--   $$
--
--   This real-valued division form of Eliahou's Lemma 2.2 holds unconditionally for every positive compressed Collatz cycle and isolates each odd cycle entry $x_i$ in a monotone decreasing factor $3 + 1/x_i$.
--
--   **Formalization Note** Stated in the `Eliahou1993` namespace (`Eliahou1993.eliahou_product_formula_real`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 48, Lemma 2.2; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/ProductFormula.lean#L127-L133 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

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
import Mathlib.Data.Real.Basic

open Finset BigOperators Eliahou1993

theorem Eliahou1993.eliahou_product_formula_real {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) = (2 : ℝ) ^ L := by sorry
