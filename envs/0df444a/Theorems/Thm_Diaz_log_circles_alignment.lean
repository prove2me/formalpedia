-- Prove2me | Theorems.Thm_Diaz_log_circles_alignment
-- name    : Diaz.log_circles_alignment
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:15.840084+00:00
-- url     : https://prove2.me/theorems/c264aeaa-213b-4f0f-bb1f-effc2c5341b7
-- title:
--   Rational alignment on a centred circle forces the ratio to be a square
-- statement:
--   **Source.** Carlo Perassi's corollary on concentric circles in the logarithm set, from his treatment of products of logarithms beyond the Diaz locus; unpublished apart from this node.
--
--   **What the corollary claims.** For non-zero logarithms `μ₁, μ₂` of algebraic numbers with
--   `m = |μ₂|²/|μ₁|²` rational: if `m` is not a rational square then
--   `trdeg_ℚ ℚ(μ₁, conj μ₁, μ₂, conj μ₂) ≥ 2`; and if `|μ₂| = |μ₁|` then either
--   `μ₂ ∈ {±μ₁, ± conj μ₁}` or the transcendence degree is again at least two. So every circle centred
--   at the origin meets the logarithm set in conjugate quadruples.
--
--   **What is formalised here.** The elementary half: the arithmetic that kills the two alignment
--   branches. If `μ₁ ≠ 0`, `|μ₂|² = m |μ₁|²` with `m` rational, and `μ₂` is a rational multiple `c` of
--   either `μ₁` or `conj μ₁`, then `m = c²` — so a non-square `m` excludes both branches outright — and
--   if `m = 1` then `c = ±1`, leaving precisely the four points `±μ₁, ± conj μ₁`.
--
--   The third alternative of the master dichotomy, the transcendence-degree branch, is **not**
--   formalised: it rests on Théorème 0.2 of Roy–Waldschmidt. What is published is the part that runs
--   without any transcendence input, which is also the part the corollary's proof actually spends its
--   words on.
--
--   Carlo Perassi records that for real logarithms the non-square case contains the
--   Gelfond–Schneider theorem in its Hilbert-seventh-problem form; off the real line it is reached
--   through the quadratic theorem instead.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing here was
--   withdrawn as wrong, and no statement in the dropped blocks was replaced by a corrected version.
--   It is worth recording because the argument is unconditional and short, and because a statement
--   that survives only in a superseded draft is the kind that gets lost.
--
--   **Novelty.** No novelty is claimed.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.log_circles_alignment {μ₁ μ₂ : ℂ} (h1 : μ₁ ≠ 0) {m c : ℚ}
    (hm : Complex.normSq μ₂ = (m : ℝ) * Complex.normSq μ₁)
    (halign : μ₂ = (c : ℂ) * μ₁ ∨ μ₂ = (c : ℂ) * conj μ₁) :
    m = c ^ 2 ∧ (m = 1 → μ₂ = μ₁ ∨ μ₂ = -μ₁ ∨ μ₂ = conj μ₁ ∨ μ₂ = -conj μ₁) := by sorry
