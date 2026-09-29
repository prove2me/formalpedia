-- Prove2me | Theorems.Thm_Diaz_salem_quartic_relations
-- name    : Diaz.salem_quartic_relations
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:35.316406+00:00
-- url     : https://prove2.me/theorems/26a0b418-e83a-482f-80d2-3624357d60f7
-- title:
--   Quadratic relations between a real and a purely imaginary logarithm
-- statement:
--   **Source.** Carlo Perassi's proposition on quartic Salem numbers, from his work on products of logarithms beyond the Diaz
--   locus.
--
--   **What the proposition claims.** For a Salem number `τ` of degree four, with conjugates
--   `τ, τ⁻¹, e^{±iθ}`, every non-zero rational homogeneous quadratic vanishing at the four principal
--   conjugate logarithms already vanishes on the rational plane `{(t, −t, s, −s)}`: all rational
--   quadratic relations among those logarithms are formal consequences of the two linear ones.
--
--   **What is formalised here.** The computational core, which is the restriction of the form to that
--   plane. Let `t` be non-zero real and `s` non-zero purely imaginary, standing for `log τ` and `iθ`,
--   and let `A, B, C` be rational with `A t² + B t s + C s² = 0`. Then `A = B = C = 0`.
--
--   The proof has two halves. The imaginary part of the relation is `B * t.re * s.im`, so `B = 0`
--   unconditionally — no transcendence input at all. The real part is `A t.re² = C s.im²`, and killing
--   that needs the one deep input the proposition names: the Gelfond–Schneider quotient dichotomy, that
--   an algebraic ratio of two non-zero logarithms of algebraic numbers is rational. It appears here as
--   the explicit hypothesis `hGS`, applied to `s / t`; a rational `s / t` is impossible for a purely
--   imaginary number over a real one, which closes the argument.
--
--   Taking `hGS` as a hypothesis rather than proving it is deliberate: it is the boundary between what
--   the argument supplies and what it cites, and putting it in the statement keeps that boundary visible.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9), which does not treat quartic Salem numbers; it is unpublished apart from this node. Nothing here was withdrawn as wrong. It is worth recording because the argument is unconditional and short.
--
--   **Novelty.** No novelty is claimed. Carlo Perassi describes the surrounding Salem material
--   as applications of the quadratic theorem to configurations whose linear layer is classical,
--   recorded as illustrations.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.salem_quartic_relations {t s : ℂ} (ht : t ≠ 0) (hs : s ≠ 0)
    (htR : t.im = 0) (hsI : s.re = 0)
    (hGS : IsAlgebraic ℚ (s / t) → ∃ r : ℚ, s / t = (r : ℂ))
    {A B C : ℚ} (h : (A : ℂ) * t ^ 2 + (B : ℂ) * (t * s) + (C : ℂ) * s ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by sorry
