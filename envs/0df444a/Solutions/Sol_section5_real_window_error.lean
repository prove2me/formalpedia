-- Prove2me | solution 1 for section5_real_window_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:11:02.612809+00:00
-- url     : https://prove2.me/submissions/c121bef9-c6b5-417c-9134-dec3f261c3e3

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5RealWindow
import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
import Theorems.Thm_section5_window_truncate_error
section
set_option autoImplicit false

/-! Signed middle-bit windows. The discarded low bits cause a bounded rounding error;
the omitted high bits are irrelevant inside the represented interval. -/











theorem section5_scaled_window_error (P H z : ℤ) (hP : 0 < P) (hH : 0 < H)
    (hlo : -H*P ≤ z) (hhi : z < H*P) (δ : ℝ) (hδ : 0 < δ) :
    |δ*(z:ℝ)-δ*(section5_window_truncate P H z : ℝ)| < δ*P := by
  have hh : (|z-section5_window_truncate P H z| : ℝ) < P := by
    exact_mod_cast section5_window_truncate_error P H z hP hH hlo hhi
  calc
    _ = δ*(|z-section5_window_truncate P H z| : ℝ) := by
      rw [← mul_sub,abs_mul,abs_of_pos hδ]
    _ < _ := mul_lt_mul_of_pos_left hh hδ



end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution (P H : ℤ) (hP : 0 < P) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (hx : |x| < δ*H*P) :
    |x-section5_real_window P H δ x| < δ*(P+1) := by
  let z : ℤ := ⌊x/δ⌋
  have hlo : -H*P ≤ z := by
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hδ).mpr
    have hh := (abs_lt.mp hx).1
    push_cast
    nlinarith
  have hhi : z < H*P := by
    apply Int.floor_lt.mpr
    apply (div_lt_iff₀ hδ).mpr
    have hh := (abs_lt.mp hx).2
    push_cast
    nlinarith
  have hl := mul_le_mul_of_nonneg_left (Int.floor_le (x/δ)) hδ.le
  have hh := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x/δ)) hδ
  have hzerr : |x-δ*(z:ℝ)| < δ := by
    dsimp only [z]
    rw [mul_div_cancel₀ _ (ne_of_gt hδ)] at hl hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  have he := section5_scaled_window_error P H z hP hH hlo hhi δ hδ
  calc
    _ ≤ |x-δ*(z:ℝ)|+|δ*(z:ℝ)-δ*(section5_window_truncate P H z : ℝ)| :=
      abs_sub_le _ _ _
    _ < δ+δ*P := add_lt_add hzerr he
    _ = _ := by ring
