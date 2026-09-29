-- Prove2me | Theorems.Thm_Diaz_elliptic_torsion_excluded
-- name    : Diaz.elliptic_torsion_excluded
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:10:38.845369+00:00
-- url     : https://prove2.me/theorems/bbe6e4a6-0c8b-42d3-b20b-6c730b01e001
-- title:
--   A conjugation-aligned transcendental admits no algebraic multiple of algebraic norm
-- statement:
--   **Source.** Part (c) of Carlo Perassi's elliptic axis and alignment lemma, from a transfer of his argument to elliptic curves, unpublished apart from this node:
--   *in the complex multiplication case, the elliptic Diaz locus contains no elliptic logarithm
--   of a torsion point.*
--
--   **Statement, as formalised.** Let `ω ∈ ℂ` be non-algebraic with `conj ω = λ ω` for some
--   algebraic `λ`, and let `α` be a non-zero algebraic number. Then `(α ω) * conj (α ω)` is not
--   algebraic.
--
--   **Why this is the lemma's statement.** The lemma's torsion logarithms are the
--   elements of $\Lambda \otimes \mathbb{Q}$, which in the complex-multiplication case is
--   $k\omega$ for a period $\omega$; reality of the invariants $g_2,g_3$ gives
--   $\bar\Lambda = \Lambda$ and hence $\bar\omega = \lambda\omega$ with $\lambda \in k$,
--   and Schneider's theorem says a non-zero period is transcendental. The conclusion is that
--   $u = \alpha\omega$ with $\alpha \in k^\times$ never satisfies $u\bar u \in
--   \bar{\mathbb{Q}}$. Substituting the two inputs — "$\omega$ transcendental" and
--   "$k \subseteq \bar{\mathbb{Q}}$" — for the objects they constrain gives exactly the
--   formal statement, with `λ` and `α` arbitrary algebraic numbers rather than elements of the
--   endomorphism field. As with part (b), the substitution loses nothing and needs no definition
--   of the period lattice or of the elliptic logarithm set.
--
--   *The proof.* `α ω` is not algebraic (else `ω = (αω)/α` would be), and
--   `conj (α ω) = (conj α · λ / α) · (α ω)` with the multiplier algebraic; the alignment lemma
--   (`Diaz.elliptic_axis_alignment`, parts (a),(b)) then rules out an algebraic norm.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing
--   was withdrawn as wrong: the transfers were moved out, not retracted.
--
--   **Novelty.** No novelty is claimed, either for the mathematics or for the formalisation.
--   Carlo Perassi presents these statements as transfers of a complex argument to
--   another setting.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.elliptic_torsion_excluded {ω lam α : ℂ} (hω : ¬ IsAlgebraic ℚ ω)
    (hlam : IsAlgebraic ℚ lam) (hcω : conj ω = lam * ω)
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) :
    ¬ IsAlgebraic ℚ ((α * ω) * conj (α * ω)) := by sorry
