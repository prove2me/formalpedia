-- Prove2me | Theorems.Thm_FamousTheorems_riemann_zeta_deriv_zero_7b
-- name    : FamousTheorems.riemann_zeta_deriv_zero_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:21.928983+00:00
-- url     : https://prove2.me/theorems/05b9a1ee-b345-473b-a750-ef6454284605
-- title:
--   ζ′(0) = −log(2π)/2
-- statement:
--   **The derivative of the Riemann zeta function at $0$.**
--   $$\zeta'(0)=-\tfrac12\log(2\pi).$$
--
--   With $\zeta(0)=-\tfrac12$ this gives the Laurent expansion $\zeta(s)=-\tfrac12-\tfrac12\log(2\pi)\,s+O(s^2)$ at $s=0$. In the theory of zeta-regularized products it gives $\prod_{n\ge1}n=\sqrt{2\pi}$, which is used in string theory and in the regularized determinants of Laplacians. The value follows from the functional equation and the Laurent expansion of $\zeta$ at $s=1$, or from the Hurwitz zeta function and Lerch's formula.
--
--   **Formalization note.** Mathlib's `deriv_riemannZeta_zero`. `deriv riemannZeta 0` is the complex derivative of Mathlib's `riemannZeta` at $0$, and `Complex.log` is the principal logarithm.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `deriv_riemannZeta_zero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riemann_zeta_deriv_zero_7b : deriv riemannZeta 0 = -Complex.log (2 * (Real.pi : ℂ)) / 2 := by sorry

end FamousTheorems
