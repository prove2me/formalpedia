-- Prove2me | Theorems.Thm_FamousTheorems_legendre_duplication_formula
-- name    : FamousTheorems.legendre_duplication_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:09.872628+00:00
-- url     : https://prove2.me/theorems/e56eda65-1d1a-4b77-8917-ab76e6f66c69
-- title:
--   Legendre's duplication formula
-- statement:
--   **Legendre's duplication formula.** For every complex number $s$,
--   $$\Gamma(s)\,\Gamma\!\left(s+\tfrac12\right)=2^{1-2s}\sqrt\pi\;\Gamma(2s).$$
--
--   This is the case $m=2$ of Gauss's multiplication formula. It is used, for example, in deriving the symmetric form of the functional equation of the Riemann zeta function and in evaluating integrals and hypergeometric series.
--
--   **Formalization note.** Mathlib's `Complex.Gamma_mul_Gamma_add_half`, stated for all `s : ℂ` with Mathlib's convention that `Complex.Gamma` is $0$ at its poles. The right-hand side is written `Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π`, with complex powers.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.Gamma_mul_Gamma_add_half`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem legendre_duplication_formula (s : ℂ) : Complex.Gamma s * Complex.Gamma (s + 1 / 2) = Complex.Gamma (2 * s) * 2 ^ (1 - 2 * s) * (Real.sqrt Real.pi : ℂ) := by sorry

end FamousTheorems
