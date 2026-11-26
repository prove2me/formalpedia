-- Prove2me | solution 1 for section5_gaussian_grid_tail_230
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:21.116788+00:00
-- url     : https://prove2.me/submissions/95f1737f-19e5-4ef2-82ba-fa1b0700aa86

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
import Theorems.Thm_section5_gaussian_cube_tail
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

/-! Gaussian density and tail estimates for Appendix D, Eq. 230. -/

































theorem section5_grid_radius_sq (M : ℕ) (hM : 0 < M) : (gridRadius M)^2 = Real.pi*M := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  unfold gridRadius gridSpacing
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity)]
  field_simp
  ring









end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example
theorem solution (n M : ℕ) (hM : 0 < M) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x : Fin n → ℝ | ∃ i, gridRadius M ≤ |x i|} ≤
        2*n*Real.exp (-Real.pi*M/2) := by
  have hL : 0 ≤ gridRadius M := by unfold gridRadius gridSpacing; positivity
  simpa only [section5_grid_radius_sq M hM,neg_mul] using section5_gaussian_cube_tail n (gridRadius M) hL
