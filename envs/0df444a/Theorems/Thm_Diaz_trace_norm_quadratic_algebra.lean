-- Prove2me | Theorems.Thm_Diaz_trace_norm_quadratic_algebra
-- name    : Diaz.trace_norm_quadratic_algebra
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:22.76956+00:00
-- url     : https://prove2.me/theorems/7830b257-8bec-4363-9f58-b0f314cfdc1b
-- title:
--   The cosine rule is an identity of quadratic algebras
-- statement:
--   **Source.** Carlo Perassi's mathematics: an identity displayed in his p-adic analogue of the argument. It is the identity that
--   carries the archimedean proof of algebraic-distance rigidity into a setting with no archimedean
--   absolute value.
--
--   **Statement.** Let `R` be a commutative ring and `σ : R →+* R` an involution. Write
--   `N x = x * σ x` for the norm and `Tr x = x + σ x` for the trace. Then for all `u, v ∈ R`,
--
--     `Tr (u * σ v) = N u + N v − N (u − v)`  and  `N (u * σ v) = N u * N v`.
--
--   Over `ℂ / ℝ` with `σ` complex conjugation the first identity reads
--   `2 Re(u * conj v) = |u|² + |v|² − |u − v|²`, which is the cosine rule. Carlo Perassi's point is
--   that the cosine rule "was never metric": it is the polarisation identity of the norm form of a
--   quadratic algebra, and holds verbatim over a quadratic extension of `ℚ_p`, where there is no
--   archimedean modulus and no involution of `ℂ_p` to imitate conjugation.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9), which does not treat the p-adic setting; it is unpublished apart from this node. Nothing here was withdrawn as wrong. It is worth recording because the argument is unconditional and short.
--
--   **Novelty.** No novelty is claimed. This is the polarisation identity for the norm form attached
--   to a ring involution.
--
--   The proof is `ring` after rewriting `σ (σ x) = x`.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.trace_norm_quadratic_algebra {R : Type*} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (u v : R) :
    (u * σ v) + σ (u * σ v)
        = u * σ u + v * σ v - (u - v) * σ (u - v)
      ∧ (u * σ v) * σ (u * σ v) = (u * σ u) * (v * σ v) := by sorry
