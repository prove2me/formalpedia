-- Prove2me | Theorems.Thm_Diaz_conj_not_linear_of_I
-- name    : Diaz.conj_not_linear_of_I
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:20.217327+00:00
-- url     : https://prove2.me/theorems/4712971d-d5b1-41e5-900d-95fd31268d6d
-- title:
--   Complex conjugation does not commute with multiplication by $i$
-- statement:
--   For the imaginary unit $i \in \mathbb{C}$,
--
--   $$\neg\ \Big(\forall\, z \in \mathbb{C}, \quad \overline{i z} = i\,\bar z\Big).$$
--
--   **Why.** Conjugation is conjugate-linear, not linear: $\overline{iz} = \bar i\,\bar z = -i\,\bar z$, and $-i \neq i$. Taking $z = 1$ already refutes the displayed identity.
--
--   **Role.** This is the concrete instance of the previous remark: conjugation is not linear over *any* base field containing $i$ — in particular not over $\bar{\mathbb{Q}}$, the base that Diaz's modulus conjecture is about. It is recorded because an earlier draft of the accompanying note asserted the opposite in the guise of calling the involution on the hull a $\bar{\mathbb{Q}}$-algebra involution.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Closure.lean#L115-L121

import Mathlib

open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

theorem Diaz.conj_not_linear_of_I :
    ¬ (∀ z : ℂ, conj (Complex.I * z) = Complex.I * conj z) := by sorry
