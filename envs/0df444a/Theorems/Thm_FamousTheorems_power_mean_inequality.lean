-- Prove2me | Theorems.Thm_FamousTheorems_power_mean_inequality
-- name    : FamousTheorems.power_mean_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:49.632037+00:00
-- url     : https://prove2.me/theorems/ff94f01e-fed9-47ee-ad79-0432d001ad2c
-- title:
--   The power mean inequality
-- statement:
--   **The power mean inequality.** Let $w_i\ge0$ be weights with $\sum_i w_i=1$, $z_i\ge0$, and $p\ge1$ real. Then
--   $$\Big(\sum_i w_iz_i\Big)^p\le\sum_i w_iz_i^{\,p}.$$
--
--   Equivalently, the weighted arithmetic mean is at most the weighted power mean $M_p=\big(\sum w_iz_i^p\big)^{1/p}$. It is the case $M_1\le M_p$ of the power mean inequality and an instance of Jensen's inequality for the convex function $t\mapsto t^p$. For $p=2$ it is the quadratic–arithmetic mean inequality.
--
--   **Formalization note.** Mathlib's `Real.rpow_arith_mean_le_arith_mean_rpow`, with the real power `z ^ p` (`Real.rpow`). The general comparison $M_p\le M_q$ for $p\le q$ follows by applying it to $z_i^p$ with exponent $q/p$, but is not stated here.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.rpow_arith_mean_le_arith_mean_rpow`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem power_mean_inequality {ι : Type*} (s : Finset ι) (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) : (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p := by sorry

end FamousTheorems
