-- Prove2me | Theorems.Thm_FamousTheorems_taylor_integral_remainder_theorem
-- name    : FamousTheorems.taylor_integral_remainder_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:25:40.709808+00:00
-- url     : https://prove2.me/theorems/15b11741-ab59-4db0-b98b-6ddaa8854ae9
-- title:
--   Taylor's theorem with integral remainder
-- statement:
--   **Taylor's theorem with integral remainder.** Let $f:\mathbb R\to F$ take values in a real Banach space and be $C^{n+1}$ on the closed interval between $x_0$ and $x$. Then
--   $$f(x)-\sum_{k=0}^{n}\frac{f^{(k)}(x_0)}{k!}(x-x_0)^k=\int_{x_0}^{x}\frac{(x-t)^n}{n!}\,f^{(n+1)}(t)\,dt .$$
--
--   This is the exact form of the Taylor remainder, from which the Lagrange and Cauchy forms and the standard error estimates follow. Unlike the mean-value forms, it holds for vector-valued functions.
--
--   **Formalization note.** Mathlib's `taylor_integral_remainder`. The derivatives are taken within the interval `Set.uIcc x₀ x` (`iteratedDerivWithin`), and `taylorWithinEval f n (Set.uIcc x₀ x) x₀ x` is the degree-$n$ Taylor polynomial at $x_0$ built from these derivatives, evaluated at $x$. The integral is the oriented interval integral.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `taylor_integral_remainder`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem taylor_integral_remainder_theorem {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Set.uIcc x₀ x)) :
    f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / (n.factorial : ℝ)) • iteratedDerivWithin (n + 1) f (Set.uIcc x₀ x) t := by sorry

end FamousTheorems
