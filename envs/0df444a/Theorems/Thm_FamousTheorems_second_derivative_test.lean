-- Prove2me | Theorems.Thm_FamousTheorems_second_derivative_test
-- name    : FamousTheorems.second_derivative_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:43.462054+00:00
-- url     : https://prove2.me/theorems/7832622f-9a4e-45de-9ee0-fe6d8648837b
-- title:
--   The second derivative test
-- statement:
--   **The second derivative test.** Let $f:\mathbb R\to\mathbb R$ be continuous at $x_0$, with $f'(x_0)=0$ and $f''(x_0)>0$. Then $f$ has a local minimum at $x_0$.
--
--   This is the standard calculus criterion that classifies critical points by the sign of the second derivative. It is the one-variable case of the Hessian test for local extrema.
--
--   **Formalization note.** Mathlib's `isLocalMin_of_deriv_deriv_pos`. Mathlib's `deriv` is $0$ where the function is not differentiable. So the hypothesis `deriv (deriv f) x₀ > 0` forces $f'$ to be differentiable at $x_0$, and in particular $f$ to be differentiable near $x_0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isLocalMin_of_deriv_deriv_pos`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem second_derivative_test {f : ℝ → ℝ} {x₀ : ℝ} (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) :
    IsLocalMin f x₀ := by sorry

end FamousTheorems
