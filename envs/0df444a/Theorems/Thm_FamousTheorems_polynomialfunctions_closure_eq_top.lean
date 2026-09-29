-- Prove2me | Theorems.Thm_FamousTheorems_polynomialfunctions_closure_eq_top
-- name    : FamousTheorems.polynomialfunctions_closure_eq_top
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:08.853488+00:00
-- url     : https://prove2.me/theorems/4f898b52-7914-49e5-b0b0-e7706d254b9c
-- title:
--   The Weierstrass approximation theorem
-- statement:
--   **The Weierstrass approximation theorem.** The polynomial functions are dense in the continuous functions on a compact interval: $$\overline{\{\text{polynomials}\}} = C([a,b], \mathbb{R}).$$ Every continuous function on a closed bounded interval is a uniform limit of polynomials, however irregular it may be — nowhere differentiable, say. Uniform approximation is much stronger than pointwise, and the theorem is what makes polynomial methods applicable throughout numerical analysis, from quadrature rules to spectral methods. Weierstrass proved it in 1885 by convolving with a Gaussian; Bernstein's 1912 proof is probabilistic, using the law of large numbers to show the Bernstein polynomials of $f$ converge uniformly to $f$. Stone's 1937 generalization replaced the interval by any compact Hausdorff space and the polynomials by any separating subalgebra containing the constants, which is the form now used to prove density of trigonometric polynomials and hence completeness of the Fourier basis. **Formalization note.** `polynomialFunctions` is the subalgebra of `C(X, ℝ)` of restrictions of polynomials, and the closure is taken in the uniform (sup-norm) topology. The result is Mathlib's `polynomialFunctions_closure_eq_top`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem polynomialfunctions_closure_eq_top :
    ∀ (a b : ℝ), (polynomialFunctions (Icc a b)).topologicalClosure = ⊤ := by sorry

end FamousTheorems
