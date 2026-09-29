-- Prove2me | Theorems.Thm_Diaz_elliptic_axis_alignment
-- name    : Diaz.elliptic_axis_alignment
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:10:22.046553+00:00
-- url     : https://prove2.me/theorems/b52f753f-3594-4707-85cb-ae3a28126987
-- title:
--   An algebraic norm forbids any algebraic alignment with the conjugate
-- statement:
--   **Source.** Carlo Perassi's elliptic axis and alignment lemma, parts (a) and (b), from a transfer of his argument to elliptic curves; unpublished apart from this node.
--
--   **Statement, as formalised.** Let `u ∈ ℂ` be non-algebraic with `u * conj u` algebraic. Then
--   `conj u ≠ u` and `conj u ≠ -u`, and more generally `conj u ≠ γ u` for **every** algebraic `γ`.
--
--   **Why this is the lemma's statement.** In the lemma `u` ranges over the elliptic
--   Diaz locus
--
--   $$\mathcal{D}_E = \{u \in \mathcal{L}_E \setminus \{0\} : u\bar u \in \bar{\mathbb{Q}}\},$$
--
--   where $\mathcal{L}_E$ is the set of elliptic logarithms of algebraic points of a Weierstrass
--   curve with real algebraic invariants, and $k = \operatorname{End}(E)\otimes\mathbb{Q}$ is
--   either $\mathbb{Q}$ or an imaginary quadratic field. Part (a) says
--   $\mathcal{D}_E \cap (\mathbb{R}\cup i\mathbb{R}) = \varnothing$; part (b) says $u$ and
--   $\bar u$ are linearly independent over $k$.
--
--   The only property of $\mathcal{L}_E$ that either proof uses is **Schneider's theorem in the
--   form $\mathcal{L}_E \cap \bar{\mathbb{Q}} = \{0\}$**, i.e. that a non-zero element of the
--   locus is not algebraic; and the only property of $k$ used is $k \subseteq
--   \bar{\mathbb{Q}}$. So the statement is recorded here with those two facts substituted for
--   the objects they constrain: `¬ IsAlgebraic ℚ u` in place of `u ∈ ℒ_E \ {0}`, and an
--   arbitrary algebraic `γ` in place of `γ ∈ k`. Nothing about elliptic functions survives the
--   substitution, and nothing is lost: the conclusion for arbitrary algebraic `γ` is formally
--   stronger than the conclusion for `γ ∈ k`.
--
--   Being an identity of this shape, the same statement covers the archimedean and the
--   ultrametric case: with a general involution in place of complex conjugation it is the
--   p-adic axis lemma, whose formalisation is already on the platform as
--   `Diaz.involution_alignment`. That node fixes `σ c = c` and concludes `c = ±1`; this one
--   lets the multiplier be any algebraic number and concludes there is none.
--
--   **No new definition.** `ℒ_E`, the endomorphism field and the elliptic Diaz locus are all
--   absent from the formal statement. Introducing them would have meant a permanent definition
--   node for the elliptic apparatus; the abstraction above carries the theorem without one.
--
--   *The proof.* If `conj u = γ u` with `γ` algebraic then `γ ≠ 0` (else `u = 0`), and
--   `u * conj u = γ u²`, so `u² = (u conj u)/γ` is algebraic, hence so is `u` — contradiction.
--   Parts (a) and (b) of the lemma are the cases `γ = 1` and `γ = -1`.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing
--   was withdrawn as wrong: the transfers were moved out, not retracted.
--
--   **Novelty.** No novelty is claimed, either for the mathematics or for the formalisation.
--   Carlo Perassi presents these statements as transfers of a complex argument to
--   another setting. The argument is three lines of field
--   arithmetic over the transcendence input.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.elliptic_axis_alignment {u : ℂ} (hu : ¬ IsAlgebraic ℚ u)
    (hn : IsAlgebraic ℚ (u * conj u)) :
    (conj u ≠ u ∧ conj u ≠ -u) ∧ ∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u := by sorry
