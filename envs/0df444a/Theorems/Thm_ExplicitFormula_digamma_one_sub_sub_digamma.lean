-- Prove2me | Theorems.Thm_ExplicitFormula_digamma_one_sub_sub_digamma
-- name    : ExplicitFormula.digamma_one_sub_sub_digamma
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:42.118271+00:00
-- url     : https://prove2.me/theorems/5a5fb1e3-ba74-4515-a703-0d13cd026a33
-- title:
--   Reflection formula for the digamma function: $\psi(1-z)-\psi(z)=\pi\cot(\pi z)$ for $z\notin\mathbb Z$
-- statement:
--   **Reflection formula for the digamma function.**
--
--   Let $\psi=\Gamma'/\Gamma$ be the digamma function, a meromorphic function on $\mathbb C$ whose poles are the points $0,-1,-2,\dots$. For every complex number $z$ which is not an integer,
--   $$\psi(1-z)-\psi(z)=\pi\cot(\pi z).$$
--
--   This is the logarithmic derivative of Euler's reflection formula $\Gamma(z)\Gamma(1-z)=\pi/\sin(\pi z)$. The source writes it in the form
--   $$\psi(1-z)-\psi(z)-\frac1z=\pi\cot(\pi z)-\frac1z\qquad(z\in\mathbb C\setminus\mathbb Z)$$
--   (equation (B.4.1.27)) and combines it with the partial fraction series of $\psi$ to obtain the expansion of $(1-e^{2\pi i z})^{-1}$ in Lemma B.4.1.9, which in turn gives the partial fraction expansion of the logarithmic derivative of a local Euler factor $(1-\chi(\mathfrak p)N(\mathfrak p)^{-s})^{-1}$.
--
--   **Formalization Note.** `Complex.digamma` is Mathlib's `logDeriv Complex.Gamma` and `Complex.cot z = Complex.cos z / Complex.sin z`. The hypothesis $z\notin\mathbb Z$ is `∀ n : ℤ, z ≠ n`; it is necessary, since at an integer one of the two arguments is a pole of $\Gamma$ (where Mathlib's `digamma` takes a junk value) and $\cot(\pi z)$ has a pole.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 612, proof of Lemma B.4.1.9, eq. (B.4.1.27)

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace ExplicitFormula

theorem digamma_one_sub_sub_digamma (z : ℂ) (hz : ∀ n : ℤ, z ≠ n) :
    Complex.digamma (1 - z) - Complex.digamma z = π * Complex.cot (π * z) := by sorry

end ExplicitFormula
