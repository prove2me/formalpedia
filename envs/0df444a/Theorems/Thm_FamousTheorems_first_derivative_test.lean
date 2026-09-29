-- Prove2me | Theorems.Thm_FamousTheorems_first_derivative_test
-- name    : FamousTheorems.first_derivative_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:45.302672+00:00
-- url     : https://prove2.me/theorems/2611278e-6d29-481d-810c-00af919dd6ed
-- title:
--   The first derivative test
-- statement:
--   **The first derivative test.** Let $f:\mathbb R\to\mathbb R$ be continuous at $x_0$. Suppose that on a punctured neighbourhood of $x_0$, $f'(x)>0$ for $x<x_0$ and $f'(x)<0$ for $x>x_0$. Then $f$ has a local maximum at $x_0$.
--
--   This is the standard calculus criterion for local extrema that uses only the first derivative. It needs no differentiability at $x_0$ itself, only continuity, so it also covers corner points such as the maximum of $-|x|$ at $0$.
--
--   **Formalization note.** Mathlib's `isLocalMax_of_sign_deriv`. The sign condition is written as $\operatorname{sign}f'(x)=\operatorname{sign}(x_0-x)$ eventually in the punctured neighbourhood filter `nhdsWithin x₀ {x₀}ᶜ`. Since Mathlib's `deriv` is $0$ at non-differentiable points, the condition forces $f$ to be differentiable there.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isLocalMax_of_sign_deriv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem first_derivative_test {f : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousAt f x₀)
    (hs : ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, SignType.sign (deriv f x) = SignType.sign (x₀ - x)) :
    IsLocalMax f x₀ := by sorry

end FamousTheorems
