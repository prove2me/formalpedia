-- Prove2me | Theorems.Thm_FamousTheorems_sum_lt_prod
-- name    : FamousTheorems.sum_lt_prod
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:12:46.785011+00:00
-- url     : https://prove2.me/theorems/eada769e-cfb8-4315-8f12-8fdf49721cb9
-- title:
--   König's theorem (set theory)
-- statement:
--   **Konig's theorem** for cardinals. If $\kappa_i < \lambda_i$ for every $i$, then $$\sum_i \kappa_i < \prod_i \lambda_i.$$ A strict inequality survives infinite summation and multiplication, which is rare in cardinal arithmetic where strictness usually collapses. Cantor's theorem is the case $\kappa_i = 1$, $\lambda_i = 2$. The most-used corollary is $\kappa < \kappa^{\mathrm{cf}(\kappa)}$, bounding cofinality and showing the continuum cannot equal $\aleph_\omega$. The proof is a diagonal argument and uses the axiom of choice. **Formalization note.** Sums and products are over `Cardinal`. The result is Mathlib's `Cardinal.sum_lt_prod`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem sum_lt_prod :
    ∀ {ι : Type u_1} (f g : ι → Cardinal.{u_2}), 
    (∀ (i : ι), f i < g i) → Cardinal.sum f < Cardinal.prod g := by sorry

end FamousTheorems
