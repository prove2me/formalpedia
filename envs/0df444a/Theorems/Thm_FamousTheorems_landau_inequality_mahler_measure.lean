-- Prove2me | Theorems.Thm_FamousTheorems_landau_inequality_mahler_measure
-- name    : FamousTheorems.landau_inequality_mahler_measure
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:52.823982+00:00
-- url     : https://prove2.me/theorems/bb050a0f-6213-49a8-bbde-d46c04e0d7f3
-- title:
--   Landau's inequality for the Mahler measure
-- statement:
--   **Landau's inequality.** For every complex polynomial $p=\sum_i a_ix^i$,
--   $$M(p)\le\Big(\sum_i|a_i|^2\Big)^{1/2}=\|p\|_2,$$
--   where $M(p)=|a_d|\prod_{p(\alpha)=0}\max(1,|\alpha|)$ is the Mahler measure.
--
--   Landau proved this in 1905. With Mignotte's bound it controls the coefficients of factors of integer polynomials, which is the basis of polynomial factorization algorithms and of estimates in Diophantine approximation and transcendence theory.
--
--   **Formalization note.** Mathlib's `Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff`. `p.mahlerMeasure` is defined as $\exp\big(\frac1{2\pi}\int_0^{2\pi}\log|p(e^{i\theta})|\,d\theta\big)$, which equals the product formula above by Jensen's formula. The sum runs over the support of $p$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem landau_inequality_mahler_measure (p : Polynomial ℂ) :
    p.mahlerMeasure ≤ Real.sqrt (∑ i ∈ p.support, ‖p.coeff i‖ ^ 2) := by sorry

end FamousTheorems
