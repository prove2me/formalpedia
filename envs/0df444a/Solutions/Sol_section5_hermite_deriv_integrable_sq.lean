-- Prove2me | solution 1 for section5_hermite_deriv_integrable_sq
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:00.893961+00:00
-- url     : https://prove2.me/submissions/3c868e22-ae35-45e4-8853-f3e9f378de29

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
import Theorems.Thm_section5_wave_sum_integrable_product
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite
theorem solution {D : ℕ} (c : Fin D → ℝ) :
    Integrable (fun x => (section5_hermite_series_deriv c x)^2) := by
  have hlo : Integrable (fun x => (section5_hermite_lower c x)^2) := by
    simpa only [section5_hermite_lower, pow_two] using
      section5_wave_sum_integrable_product (fun k => c k*Real.sqrt k)
        (fun k => c k*Real.sqrt k) (fun k : Fin D => (k:ℕ)-1) (fun k => (k:ℕ)-1)
  have hhi : Integrable (fun x => (section5_hermite_upper c x)^2) := by
    simpa only [section5_hermite_upper, pow_two] using
      section5_wave_sum_integrable_product (fun k => c k*Real.sqrt ((k:ℕ)+1))
        (fun k => c k*Real.sqrt ((k:ℕ)+1)) (fun k : Fin D => (k:ℕ)+1) (fun k => (k:ℕ)+1)
  have hcross : Integrable (fun x => section5_hermite_lower c x*section5_hermite_upper c x) :=
    section5_wave_sum_integrable_product _ _ _ _
  have heq : (fun x => (section5_hermite_series_deriv c x)^2) =
      fun x => ((section5_hermite_lower c x)^2 -
        2*(section5_hermite_lower c x*section5_hermite_upper c x) +
          (section5_hermite_upper c x)^2)/4 := by
    funext x
    unfold section5_hermite_series_deriv
    ring
  rw [heq]
  exact ((hlo.sub (hcross.const_mul 2)).add hhi).div_const 4
