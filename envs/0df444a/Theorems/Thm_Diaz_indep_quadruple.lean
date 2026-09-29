-- Prove2me | Theorems.Thm_Diaz_indep_quadruple
-- name    : Diaz.indep_quadruple
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:23.454514+00:00
-- url     : https://prove2.me/theorems/484f4963-3b2c-42cd-b98e-5de60c21ca6f
-- title:
--   Two independent candidates have a ℚ-independent conjugate quadruple
-- statement:
--   **Source.** Carlo Perassi's proposition giving an independence certificate on the Diaz locus, from his treatment of products of logarithms beyond the Diaz locus; unpublished apart from this node.
--
--   **What the proposition claims.** If `u` and `v` are points of the Diaz locus that are algebraically
--   independent over `ℚ`, then `u, conj u, v, conj v` are linearly independent over `ℚ`. The point of
--   the proposition is that the linear-independence certificate demanded by the independence-upgrade
--   lemma is automatic on the Diaz locus once the pair dichotomy has been applied.
--
--   **Statement formalised.** Let `K` be a subfield of `ℂ` (the intended `K` is `ℚ̄`), let `u, v` be
--   non-zero with `u * conj u ∈ K` and `v * conj v ∈ K` — this is the Diaz condition — and suppose `u`
--   is transcendental over `K` and `v` is transcendental over the hull `K(u)`. Then any rational
--   relation `a u + b conj u + c v + d conj v = 0` has `a = b = c = d = 0`.
--
--   The two transcendence hypotheses are what the proposition's proof actually uses; they follow from
--   algebraic independence of `u` and `v` over `ℚ` together with `K` algebraic. Stating them directly
--   keeps the node free of a `ℚ̄`-algebraicity side condition.
--
--   **The mechanism.** Substituting `conj u = (u conj u)/u` and `conj v = (v conj v)/v` and clearing
--   denominators turns the relation into
--   `(c u) v² + (a u² + b (u conj u)) v + (d (v conj v) u) = 0`, a quadratic in `v` with coefficients
--   in `K(u)`. Transcendence of `v` over `K(u)` kills all three: `c = 0` and `d = 0` at once, and
--   `a u² + b (u conj u) = 0` with `a ≠ 0` would make `u` a root of `X² + (b/a)(u conj u)` over `K`,
--   contradicting transcendence of `u`. So `a = 0`, and then `b = 0`.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing here was
--   withdrawn as wrong, and no statement in the dropped blocks was replaced by a corrected version.
--   It is worth recording because the argument is unconditional and short, and because a statement
--   that survives only in a superseded draft is the kind that gets lost.
--
--   **Novelty.** No novelty is claimed. Carlo Perassi presents this as bookkeeping that makes an
--   existing lemma of Waldschmidt applicable, not as a result.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.indep_quadruple {K : Subfield ℂ} {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hq : u * conj u ∈ K) (hq' : v * conj v ∈ K)
    (hut : Transcendental (↥K) u)
    (hvt : Transcendental (↥(hull K u)) v)
    {a b c d : ℚ}
    (h : (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * v + (d : ℂ) * conj v = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by sorry
