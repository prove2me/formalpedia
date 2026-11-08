-- Prove2me | Theorems.Thm_Eliahou1993_eliahou_theorem_1_1
-- name    : Eliahou1993.eliahou_theorem_1_1
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:57.967065+00:00
-- url     : https://prove2.me/theorems/3befb9ae-6725-465f-af88-a8be2c4a34d8
-- title:
--   Eliahou (1993) Theorem 1.1: conditional linear form for compressed Collatz cycle cardinality
-- statement:
--   Let $c = (x_0, x_1, \dots, x_{L-1})$ be an injective cycle of length $L > 0$ of the compressed Collatz map $T$, with orbit set $\Omega = \{x_0, x_1, \dots, x_{L-1}\}$ and minimum element $m = \min \Omega$. Conditional on the hypothesis that $m > 2^{40}$, there exist nonnegative integers $a, b, c_{\mathrm{coeff}} \in \mathbb{N}$ such that
--
--   $$
--   b > 0, \quad a \cdot c_{\mathrm{coeff}} = 0, \quad \text{and} \quad |\Omega| = 301{,}994\, a + 17{,}087{,}915\, b + 85{,}137{,}581\, c_{\mathrm{coeff}}.
--   $$
--
--   This is the main result (Theorem 1.1) of Eliahou (1993), expressing the exact cardinality $|\Omega|$ of any compressed Collatz cycle whose minimum exceeds $2^{40}$ as a positive integer combination of consecutive continued-fraction convergent numerators of $\log_2 3$.
--
--   **Formalization Note** This theorem is **conditional** on the explicit hypothesis `(2 : ℕ) ^ 40 < cyc.minElem` (along with injectivity `Function.Injective cyc.seq` so that $|\Omega| = L$), which is assumed as an explicit hypothesis and not certified on the platform. Stated in the `Eliahou1993` namespace (`Eliahou1993.eliahou_theorem_1_1`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 46 & p. 51, Theorem 1.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/LinearForm.lean#L173-L181 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/LinearForm.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Theorem 1.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Definitions.Def_eliahou1993Cycle

open Finset Eliahou1993

theorem Eliahou1993.eliahou_theorem_1_1 {L : ℕ} (cyc : CollatzCycle L)
    (hinj : Function.Injective cyc.seq)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    ∃ (a b cCoeff : ℕ), 0 < b ∧ a * cCoeff = 0 ∧
      (Finset.univ.image cyc.seq).card =
        301994 * a + 17087915 * b + 85137581 * cCoeff := by sorry
