-- Prove2me | solution 1 for section5_wave_sum_integrable_product
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:17.642808+00:00
-- url     : https://prove2.me/submissions/f126b49e-c005-428b-972c-eba909549742

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
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℕ) (v : κ → ℕ) :
    Integrable (fun x => (∑ i, a i*section5_hermite_wave (u i) x)*
      (∑ j, b j*section5_hermite_wave (v j) x)) := by
  have heq : (fun x => (∑ i, a i*section5_hermite_wave (u i) x)*
      (∑ j, b j*section5_hermite_wave (v j) x)) =
      fun x => ∑ i, ∑ j, (a i*b j)*
        (section5_hermite_wave (u i) x*section5_hermite_wave (v j) x) := by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (section5_hermite_wave_integrable_product _ _).const_mul _))
