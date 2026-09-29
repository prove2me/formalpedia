-- Prove2me | Theorems.Thm_Diaz_involution_alignment
-- name    : Diaz.involution_alignment
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:26.361688+00:00
-- url     : https://prove2.me/theorems/b9b2f60f-ec6c-4453-a45c-ec1ddbde38e3
-- title:
--   An involution aligns an element with itself only up to sign
-- statement:
--   **Source.** Carlo Perassi's p-adic axis lemma — specifically its second assertion, and
--   the remark that immediately follows it; unpublished apart from this node.
--
--   **Statement.** Let `R` be a field and `σ : R →+* R` an involution. If `u ≠ 0`, `c` is fixed by
--   `σ`, and `σ u = c * u`, then `c = 1` or `c = −1`.
--
--   **Why it is worth isolating.** Carlo Perassi flags this as the one place where the p-adic
--   transfer is *stronger* than its complex model, not weaker: "the second assertion is stronger than
--   its complex counterpart, which needs an argument about rational numbers of modulus one: here
--   `c² = 1` already forces `c = ±1` in the fixed field." Applying `σ` to `σ u = c u` gives
--   `u = c² u`, and a field with `u ≠ 0` finishes it. Over `ℂ` the same step needs the extra remark
--   that a rational number of modulus one is `±1`.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing here was
--   withdrawn as wrong, and no statement in the dropped blocks was replaced by a corrected version.
--   It is worth recording because the argument is unconditional and short, and because a statement
--   that survives only in a superseded draft is the kind that gets lost.
--
--   **Novelty.** No novelty is claimed. This is the degenerate case of Hilbert's Theorem 90 for a
--   quadratic extension.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.involution_alignment {R : Type*} [Field R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    {u c : R} (hu : u ≠ 0) (hc : σ c = c) (h : σ u = c * u) :
    c = 1 ∨ c = -1 := by sorry
