-- Prove2me | solution 1 for mme_dwz_affine_retaining_state_w0_eq_conditioned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T00:17:39.825447+00:00
-- url     : https://prove2.me/submissions/956fed10-5ff9-482e-bb3d-afd1ac4cd1d4

import Theorems.Thm_mme_dwz_asymmetric_affine_retains_iff_weight_label

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = (4 : ZMod p))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (hretains : MME.dwzAsymmetricAffineRetains
      (4 : ZMod p) S I J K q) :
    q.2 =
      2 * (∑ t : Fin (N + 1), I t * q.1 t.castSucc) -
        ∑ t : Fin (N + 1),
          ((4 : ZMod p) - K t) * q.1 t.castSucc := by
  have hnormal :=
    (mme_dwz_asymmetric_affine_retains_iff_weight_label
      hpodd (4 : ZMod p) S I J K hsupport q).mp hretains
  rw [hnormal.2]
  have hpoint (t : Fin (N + 1)) :
      (4 : ZMod p) - K t = I t + J t := by
    rw [← hsupport t]
    ring
  simp_rw [hpoint, add_mul, Finset.sum_add_distrib]
  ring
