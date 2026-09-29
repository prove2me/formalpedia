-- Prove2me | Theorems.Thm_FamousTheorems_entire_function_taylor_series
-- name    : FamousTheorems.entire_function_taylor_series
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:45.559674+00:00
-- url     : https://prove2.me/theorems/e3385c31-5ae9-4cdf-ad42-c7a88de9f73b
-- title:
--   Entire functions are represented by their Taylor series everywhere
-- statement:
--   **Entire functions are represented by their Taylor series everywhere.** Let $f:\mathbb C\to E$ be an entire function with values in a complex Banach space $E$. Then for all $c,z\in\mathbb C$,
--   $$f(z)=\sum_{n=0}^\infty\frac{f^{(n)}(c)}{n!}(z-c)^n,$$
--   and the series converges.
--
--   A holomorphic function on a disc equals its Taylor series on that disc. For an entire function the disc is the whole plane, so the Taylor series at any point converges to $f$ everywhere. Examples are $e^z$, $\sin z$, $\cos z$ and all polynomials. This is one of the main differences between complex and real differentiability.
--
--   **Formalization note.** Mathlib's `Complex.hasSum_taylorSeries_of_entire`. `iteratedDeriv n f c` is $f^{(n)}(c)$, and `HasSum` is unconditional convergence of the series.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.hasSum_taylorSeries_of_entire`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem entire_function_taylor_series {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : Differentiable ℂ f) (c z : ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by sorry

end FamousTheorems
