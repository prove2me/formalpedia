-- Prove2me | solution 1 for section5_hermite_roundCoord_norm_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:31.106804+00:00
-- url     : https://prove2.me/submissions/92fd11dd-d648-4254-ad63-4ed910defdf7

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
import Theorems.Thm_section5_hermite_roundCoord_error
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite
theorem solution {D : ℕ} (c : Fin D → ℂ)
    (hc : ∑ k, ‖c k‖^2 = 1) (M : ℕ) (hM : 0 < M) :
    Real.sqrt (∫ x in (-QuantumLTF.Example.gridRadius M)..(QuantumLTF.Example.gridRadius M),
      ‖section5_complex_hermite_series c x-
        section5_complex_hermite_series c (QuantumLTF.Example.roundCoord M x)‖^2) ≤
          Real.sqrt (16*(D+1)/M) := by
  apply Real.sqrt_le_sqrt
  simpa only [hc, mul_one] using section5_hermite_roundCoord_error c M hM
