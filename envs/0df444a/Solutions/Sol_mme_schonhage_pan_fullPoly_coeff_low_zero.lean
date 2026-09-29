-- Prove2me | solution 1 for mme_schonhage_pan_fullPoly_coeff_low_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:10:29.898123+00:00
-- url     : https://prove2.me/submissions/8b0565ab-1de2-4a94-8903-875fed92d62a

import Theorems.Thm_mme_schonhage_pan_sidePoly_coeff_zero_to_five
import Theorems.Thm_mme_schonhage_pan_sidePoly_coeff_six_to_nine
import Theorems.Thm_mme_schonhage_pan_fullPoly_coeff_ten_zero
import Theorems.Thm_mme_schonhage_pan_sidePoly_coeff_eleven_zero

open BigOperators Finset Polynomial

universe u


/-!
Degree-range assembly for the scalar half of Pan's order-12 certificate.
Each imported child is a separately verifiable finite polynomial calculation.
-/

theorem solution
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) (n : ℕ) (hn : n < 12) :
    (PanLeanBridge.fullPoly (K := K) q0 q1 q2).coeff n = 0 := by
  by_cases h6 : n < 6
  · simp only [PanLeanBridge.fullPoly, Polynomial.finset_sum_coeff]
    exact Finset.sum_eq_zero (fun s _ =>
      mme_schonhage_pan_sidePoly_coeff_zero_to_five q0 q1 q2 s n h6)
  by_cases h10 : n < 10
  · simp only [PanLeanBridge.fullPoly, Polynomial.finset_sum_coeff]
    exact Finset.sum_eq_zero (fun s _ =>
      mme_schonhage_pan_sidePoly_coeff_six_to_nine q0 q1 q2 s n (by omega) h10)
  by_cases hten : n = 10
  · subst n
    exact mme_schonhage_pan_fullPoly_coeff_ten_zero q0 q1 q2
  have heleven : n = 11 := by omega
  subst n
  simp only [PanLeanBridge.fullPoly, Polynomial.finset_sum_coeff]
  exact Finset.sum_eq_zero (fun s _ =>
    mme_schonhage_pan_sidePoly_coeff_eleven_zero q0 q1 q2 s)
