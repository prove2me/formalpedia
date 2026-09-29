-- Prove2me | solution 1 for mme_schonhage_pan_Phi_coeff_low_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:10:30.4246+00:00
-- url     : https://prove2.me/submissions/69eaaf6e-5fba-4595-a6e4-e2087706afc9

import Theorems.Thm_mme_schonhage_pan_fullPoly_coeff_low_zero
import Theorems.Thm_mme_schonhage_pan_Phi_coeff_repr

open MME PiTensorProduct BigOperators Finset Polynomial

universe u


/-!
Coordinatewise assembly of the low-coefficient theorem.  The tensor basis is
injective; the representation child turns every coordinate of `Phi.coeff n`
into `fullPoly.coeff n`, and the scalar child makes that coordinate zero.
-/

theorem solution
    {K : Type u} [Field K] (n : ℕ) (hn : n < 12) :
    (PanLeanBridge.Phi (K := K)).coeff n = 0 := by
  apply (PanLeanBridge.tensorBasis (K := K)).repr.injective
  ext q
  rw [mme_schonhage_pan_Phi_coeff_repr]
  simpa using mme_schonhage_pan_fullPoly_coeff_low_zero
    (K := K) (q 0) (q 1) (q 2) n hn
