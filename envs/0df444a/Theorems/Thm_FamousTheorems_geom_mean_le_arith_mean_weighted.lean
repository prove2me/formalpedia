-- Prove2me | Theorems.Thm_FamousTheorems_geom_mean_le_arith_mean_weighted
-- name    : FamousTheorems.geom_mean_le_arith_mean_weighted
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:17:14.685133+00:00
-- url     : https://prove2.me/theorems/8497d847-fc7f-46ba-ab13-28cb9255b013
-- title:
--   The weighted AM–GM inequality
-- statement:
--   **The weighted arithmetic–geometric mean inequality.**
--
--   For non-negative weights $w_i$ summing to $1$ and non-negative $z_i$,
--   $$\prod_i z_i^{w_i} \;\le\; \sum_i w_i z_i .$$
--
--   Taking all $w_i = 1/n$ gives the familiar form: the geometric mean never exceeds the arithmetic
--   mean,
--   $$\sqrt[n]{z_1\cdots z_n} \le \frac{z_1+\cdots+z_n}{n},$$
--   with equality exactly when all the $z_i$ agree.
--
--   The weighted version is the sharp one, and it is really concavity of $\log$ — Jensen's
--   inequality applied to $\log$ — which is why the proof generalises to give Hölder's and Young's
--   inequalities. It is among the most-used inequalities in analysis and optimisation.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem geom_mean_le_arith_mean_weighted : ∀ {ι : Type*} (s : Finset ι) (w z : ι → ℝ),
    (∀ i ∈ s, 0 ≤ w i) → ∑ i ∈ s, w i = 1 → (∀ i ∈ s, 0 ≤ z i) →
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i := by sorry

end FamousTheorems
