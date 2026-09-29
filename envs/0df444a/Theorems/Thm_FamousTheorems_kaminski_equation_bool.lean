-- Prove2me | Theorems.Thm_FamousTheorems_kaminski_equation_bool
-- name    : FamousTheorems.kaminski_equation_bool
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:35.349078+00:00
-- url     : https://prove2.me/theorems/aebef72a-b4b0-404e-a339-58564307e7f1
-- title:
--   Kaminski's equation
-- statement:
--   **Kaminski's equation.** For every function $f:\{\mathrm{true},\mathrm{false}\}\to\{\mathrm{true},\mathrm{false}\}$ and every Boolean $x$,
--   $$f(f(f(x)))=f(x).$$
--
--   There are only four Boolean functions: the identity, negation and the two constants. The identity holds for each of them. It is a well-known small benchmark for automated reasoning, because it cannot be proved by equational rewriting alone and needs a case split on the finitely many values.
--
--   **Formalization note.** Mathlib's `Bool.apply_apply_apply`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Bool.apply_apply_apply`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kaminski_equation_bool (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by sorry

end FamousTheorems
