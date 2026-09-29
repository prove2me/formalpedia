-- Prove2me | solution 1 for mme_dwz_threeAP_free_cast_labels_collapse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:59:42.695513+00:00
-- url     : https://prove2.me/submissions/7725bd7e-c9bb-4cd1-99d4-f41f8cda89c6

import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (p : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (x y z : ℕ) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hAP : (x : ZMod p) + (y : ZMod p) = 2 * (z : ZMod p)) :
    x = z ∧ z = y := by
  exact mme_threeAP_free_half_modulus_no_collision
    p S hSrange hSfree x z y hx hz hy hAP
