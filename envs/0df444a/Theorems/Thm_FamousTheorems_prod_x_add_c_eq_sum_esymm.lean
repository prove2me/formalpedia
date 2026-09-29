-- Prove2me | Theorems.Thm_FamousTheorems_prod_x_add_c_eq_sum_esymm
-- name    : FamousTheorems.prod_x_add_c_eq_sum_esymm
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:48.750042+00:00
-- url     : https://prove2.me/theorems/01a0b1d4-1bfa-4471-944b-1551560605d6
-- title:
--   Vieta's formulas
-- statement:
--   **Vieta's formulas.** Expanding a product of linear factors, $$\prod_i (X + r_i) = \sum_k e_k(r)\,X^{n-k},$$ so the coefficients of a monic polynomial are the elementary symmetric functions of its roots, up to sign. The relations between roots and coefficients are therefore completely explicit: the sum of the roots is minus the second coefficient, the product is $\pm$ the constant term. Because the $e_k$ are symmetric, the coefficients are invariant under permuting roots — the observation from which Galois theory begins. Vieta published the formulas around 1590. **Formalization note.** The product is over a multiset of roots and `esymm` is the elementary symmetric function. The result is Mathlib's `Multiset.prod_X_add_C_eq_sum_esymm`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem prod_x_add_c_eq_sum_esymm :
    ∀ {R : Type u_1} [inst : CommSemiring R] (s : Multiset R), 
    (Multiset.map (fun r => Polynomial.X + Polynomial.C r) s).prod = 
    ∑ j ∈ Finset.range (s.card + 1), Polynomial.C (s.esymm j) * Polynomial.X ^ (s.card - j) := by sorry

end FamousTheorems
