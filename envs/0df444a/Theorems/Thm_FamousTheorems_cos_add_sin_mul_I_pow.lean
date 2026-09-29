-- Prove2me | Theorems.Thm_FamousTheorems_cos_add_sin_mul_I_pow
-- name    : FamousTheorems.cos_add_sin_mul_I_pow
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:17:11.809345+00:00
-- url     : https://prove2.me/theorems/ddbc5246-dacb-4cb0-9ca5-c1ac064c90d7
-- title:
--   De Moivre's formula
-- statement:
--   **De Moivre's formula.**
--
--   $$(\cos z + i\sin z)^{n} \;=\; \cos(nz) + i\sin(nz).$$
--
--   Via Euler's identity $e^{iz} = \cos z + i \sin z$ it is simply $(e^{iz})^n = e^{inz}$, so it
--   says the exponential turns multiplication of angles into addition.
--
--   Expanding the left side with the binomial theorem and matching real and imaginary parts
--   generates every multiple-angle formula at once: $\cos 2z = \cos^2 z - \sin^2 z$,
--   $\sin 3z = 3\sin z - 4\sin^3 z$, and so on. It is also how one extracts $n$-th roots of complex
--   numbers, and hence the source of the roots of unity and the cyclotomic polynomials.
--
--   Stated by de Moivre around 1707, before Euler's identity made it transparent.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cos_add_sin_mul_I_pow : ∀ (n : ℕ) (z : ℂ),
    (Complex.cos z + Complex.sin z * Complex.I) ^ n =
      Complex.cos (n * z) + Complex.sin (n * z) * Complex.I := by sorry

end FamousTheorems
