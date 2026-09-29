-- Prove2me | solution 1 for mme_CW_2376_supported_two_modes_determine_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:12:46.754201+00:00
-- url     : https://prove2.me/submissions/1d9beeb4-9274-4baa-ad2c-b66aeb8a3800

import Definitions.Def_mme_CW_2376_profile_induced_family

open MME

set_option autoImplicit false

/-- Pointwise grade-sum cancellation: equality in two distinct tensor modes
forces equality in the third mode. -/
theorem solution
    {m : ℕ} {a b : CW2376ProfileAddress m}
    (ha : CW2376CoordinatewiseSupported a)
    (hb : CW2376CoordinatewiseSupported b)
    {i k : Fin 3} (hik : i ≠ k)
    (hi : a i = b i) (hk : a k = b k) :
    a = b := by
  funext r j
  have hi_j : a i j = b i j := congrFun hi j
  have hk_j : a k j = b k j := congrFun hk j
  by_cases hri : r = i
  · simpa only [hri] using hi_j
  by_cases hrk : r = k
  · simpa only [hrk] using hk_j
  apply Fin.ext
  have hi_val : (a i j).val = (b i j).val := congrArg Fin.val hi_j
  have hk_val : (a k j).val = (b k j).val := congrArg Fin.val hk_j
  have ha_j := ha j
  have hb_j := hb j
  fin_cases i <;> fin_cases k <;> fin_cases r <;>
    simp_all <;> omega
