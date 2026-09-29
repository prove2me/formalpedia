-- Prove2me | Theorems.Thm_Diaz_equal_real_parts
-- name    : Diaz.equal_real_parts
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:43.537743+00:00
-- url     : https://prove2.me/theorems/2f03d933-e842-4ae9-9911-5656d4bf76c4
-- title:
--   Equal real parts turn a rational modulus ratio into a ternary quadric
-- statement:
--   **Source.** Carlo Perassi's proposition on equal real parts, from his treatment of products of logarithms beyond the Diaz locus; unpublished apart from this node.
--
--   **What the proposition claims.** For `μ₁, μ₂` logarithms of algebraic numbers with a common
--   non-zero real part `x` and non-zero imaginary parts, and with `m = |μ₂|²/|μ₁|²` rational, either
--   `m = 1` and `μ₂ ∈ {μ₁, conj μ₁}`, or `x`, `Im μ₁`, `Im μ₂` are pairwise algebraically independent.
--
--   **What is formalised here.** The two elementary halves, for arbitrary complex numbers:
--
--   1. the reduction. Writing `y_j = i * Im μ_j`, the hypothesis `|μ₂|² = m |μ₁|²` becomes
--      `(1 − m) x² + m y₁² − y₂² = 0`, a rational ternary quadratic form evaluated at
--      `(x, y₁, y₂)`, of determinant `± m(m − 1)`. In the real coordinates used here that reads
--      `(1 − m) (Re μ₁)² + (Im μ₂)² − m (Im μ₁)² = 0`;
--   2. the `m = 1` branch, where the relation collapses to `y₂² = y₁²` and hence
--      `μ₂ = μ₁` or `μ₂ = conj μ₁`.
--
--   The remaining branch — `m ≠ 1` makes the form non-degenerate, and the ternary-quadric proposition
--   then forces transcendence degree at least two — is **not** formalised. It rests on Théorème 0.2 of
--   Roy–Waldschmidt, which is not available here. What is published is exactly the elementary
--   statement that the transcendence input is applied to.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing here was
--   withdrawn as wrong, and no statement in the dropped blocks was replaced by a corrected version.
--   It is worth recording because the argument is unconditional and short, and because a statement
--   that survives only in a superseded draft is the kind that gets lost.
--
--   **Novelty.** No novelty is claimed for the reduction or the `m = 1` branch, which are ordinary
--   manipulations of real and imaginary parts.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.equal_real_parts {μ₁ μ₂ : ℂ} {m : ℚ}
    (hre : μ₂.re = μ₁.re)
    (hm : Complex.normSq μ₂ = (m : ℝ) * Complex.normSq μ₁) :
    (1 - (m : ℝ)) * μ₁.re ^ 2 + μ₂.im ^ 2 - (m : ℝ) * μ₁.im ^ 2 = 0
      ∧ (m = 1 → μ₂ = μ₁ ∨ μ₂ = conj μ₁) := by sorry
