-- Prove2me | Theorems.Thm_Diaz_elliptic_chords_norm_one
-- name    : Diaz.elliptic_chords_norm_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:11:05.157434+00:00
-- url     : https://prove2.me/theorems/ade5604c-b845-46e1-b17a-4f8b73466c01
-- title:
--   Equal-modulus chords land in the norm-one group of the coefficient field
-- statement:
--   **Source.** Carlo Perassi's corollary on elliptic chords (the norm-one orbit), from a transfer of his argument to elliptic curves; unpublished apart from this node.
--
--   **Statement, as formalised.** Let `k ⊆ ℂ` be a conjugation-stable subfield, `u ≠ 0`, and
--   `v = γ u` with `γ ∈ k` and `‖v‖ = ‖u‖`. Then
--
--   1. `γ conj γ = 1`;
--   2. if `k` is fixed pointwise by conjugation (the non-CM case `k = ℚ`), then `v = u` or
--      `v = -u`;
--   3. if `k` is *not* fixed pointwise (the CM case, `k` imaginary quadratic), then
--      `γ = δ / conj δ` for some non-zero `δ ∈ k` — Hilbert's Theorem 90 for the quadratic
--      extension `k/k^{conj}`.
--
--   **Where this sits.** The corollary reads: for distinct `u, v` in the elliptic
--   Diaz locus with `|u| = |v|`, one has `|u−v|` algebraic if and only if `v = γu` with
--   `γ ∈ k`, `N(γ) = 1`. The "only if" is his theorem on elliptic algebraic distance and plane rigidity, whose
--   plane half is the separate node `Diaz.elliptic_plane_rigidity` and whose distance half rests
--   on elliptic Baker; the corollary's own content, and all of it, is what happens to `γ`
--   afterwards — and that is what this node records, with `v = γ u` as the hypothesis rather
--   than the conclusion. Over `ℚ` the norm-one group is `{±1}` and one recovers the four-point
--   orbit `{±u, ±conj u}` of the complex case (on this mission: `Diaz.orbit_of_candidate`); over
--   an imaginary quadratic field, Hilbert 90 exhibits `k^{(1)}` as `{δ/conj δ}`, which is
--   infinite.
--
--   **What is *not* formalised.** The corollary closes with an analytic remark:
--   `k^{(1)}` being an infinite subgroup of the unit circle, it is dense, so a single
--   complex-multiplication candidate forces a dense set of candidates on its own circle —
--   "elliptic Diaz is empty or dense on each centered circle". Neither the infinitude of
--   `k^{(1)}` nor the density of an infinite subgroup of the circle is formalised here; this
--   node stops at the algebraic dichotomy. That remark is unaffected by anything stated above and
--   is not claimed.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing
--   was withdrawn as wrong: the transfers were moved out, not retracted.
--
--   **Novelty.** No novelty is claimed, either for the mathematics or for the formalisation.
--   Carlo Perassi presents these statements as transfers of a complex argument to
--   another setting. Part 3 is Hilbert's Theorem 90 for a
--   quadratic extension, which is classical; the proof given is the standard explicit one
--   (`δ = 1 + γ`, with the trace-zero line covering `γ = -1`).

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.elliptic_chords_norm_one {k : Subfield ℂ} (hkc : ∀ x ∈ k, conj x ∈ k)
    {u v γ : ℂ} (hu : u ≠ 0) (hγ : γ ∈ k) (hv : v = γ * u) (hmod : ‖v‖ = ‖u‖) :
    γ * conj γ = 1
      ∧ ((∀ x ∈ k, conj x = x) → v = u ∨ v = -u)
      ∧ ((∃ x ∈ k, conj x ≠ x) → ∃ δ ∈ k, δ ≠ 0 ∧ γ = δ / conj δ) := by sorry
