-- Prove2me | solution 1 for section5_hermite_lower_integral_sq
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:52.438638+00:00
-- url     : https://prove2.me/submissions/18e36513-737d-4a8d-883d-22ea218a3285

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
import Theorems.Thm_section5_wave_sum_product_integral
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite
theorem solution {D : ℕ} (c : Fin D → ℝ) :
    (∫ x : ℝ, (section5_hermite_lower c x)^2) = ∑ k, (c k)^2*(k:ℕ) := by
  classical
  unfold section5_hermite_lower
  simp_rw [pow_two]
  rw [section5_wave_sum_product_integral]
  have hterm (i j : Fin D) :
      (c i*Real.sqrt i*(c j*Real.sqrt j)) *
        (if (i:ℕ)-1=(j:ℕ)-1 then (1:ℝ) else 0) =
          if i=j then (c i)^2*(i:ℕ) else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [ite_true, mul_one]
      calc
        _ = (c i)^2*(Real.sqrt i)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    · rw [if_neg hij]
      by_cases hi : (i:ℕ)=0
      · simp [hi]
      by_cases hj : (j:ℕ)=0
      · simp [hj]
      have hne : (i:ℕ)-1 ≠ (j:ℕ)-1 := by
        intro h
        apply hij
        apply Fin.ext
        omega
      simp [hne]
  simp_rw [hterm]
  simp [pow_two]
