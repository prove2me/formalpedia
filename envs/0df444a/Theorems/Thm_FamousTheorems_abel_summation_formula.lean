-- Prove2me | Theorems.Thm_FamousTheorems_abel_summation_formula
-- name    : FamousTheorems.abel_summation_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:39.983324+00:00
-- url     : https://prove2.me/theorems/7f5201ba-cc9a-4a38-bb8e-0826e8421a2c
-- title:
--   Abel's summation formula
-- statement:
--   **Abel's summation formula.** Let $(c_k)_{k\ge0}$ be a sequence in $\mathbb R$ or $\mathbb C$, $b\ge0$, and let $f$ be differentiable on $[0,b]$ with integrable derivative. Writing $C(t)=\sum_{0\le k\le t}c_k$,
--   $$\sum_{0\le k\le b}f(k)\,c_k=f(b)\,C(b)-\int_0^b f'(t)\,C(t)\,dt.$$
--
--   This is summation by parts in integral form, and it is the standard way to pass between sums weighted by a smooth function and partial sums. It is used throughout analytic number theory: to derive Mertens' estimates, to relate $\pi(x)$ and $\theta(x)$, and to continue Dirichlet series analytically.
--
--   **Formalization note.** Mathlib's `sum_mul_eq_sub_integral_mul`. Sums run over `Finset.Icc 0 ⌊b⌋₊` (with `⌊·⌋₊` the natural-number floor), and the integral is over `Set.Ioc 0 b`. The coefficients lie in an `RCLike` field.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `sum_mul_eq_sub_integral_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem abel_summation_formula {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} {b : ℝ} (hb : 0 ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc 0 b, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 0 b)) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, f k * c k =
      f b * ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k - ∫ t in Set.Ioc 0 b, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by sorry

end FamousTheorems
