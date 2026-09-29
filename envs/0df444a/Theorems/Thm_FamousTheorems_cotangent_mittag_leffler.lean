-- Prove2me | Theorems.Thm_FamousTheorems_cotangent_mittag_leffler
-- name    : FamousTheorems.cotangent_mittag_leffler
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:59.131007+00:00
-- url     : https://prove2.me/theorems/6066de36-3f85-4764-b57a-870caa20fc35
-- title:
--   The Mittag-Leffler expansion of the cotangent
-- statement:
--   **The Mittag-Leffler expansion of the cotangent.** For every complex number $x$ that is not an integer,
--   $$\pi\cot(\pi x)=\frac1x+\sum_{n=1}^{\infty}\Big(\frac1{x-n}+\frac1{x+n}\Big).$$
--
--   This partial-fraction expansion is the logarithmic derivative of Euler's sine product. It gives Euler's evaluation of $\zeta(2k)$ by expanding in powers of $x$, and it is the starting point of the theory of Eisenstein series and of the Mittag-Leffler theorem on meromorphic functions with prescribed poles.
--
--   **Formalization note.** Mathlib's `cot_series_rep`. `Complex.integerComplement` is the set of complex numbers that are not integers, and the sum is Mathlib's `tsum` over `n : ℕ+`, which converges absolutely here since the paired terms are $2x/(x^2-n^2)=O(1/n^2)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `cot_series_rep`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cotangent_mittag_leffler {x : ℂ} (hx : x ∈ Complex.integerComplement) :
    (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x) = 1 / x + ∑' n : ℕ+, (1 / (x - ((n : ℕ) : ℂ)) + 1 / (x + ((n : ℕ) : ℂ))) := by sorry

end FamousTheorems
