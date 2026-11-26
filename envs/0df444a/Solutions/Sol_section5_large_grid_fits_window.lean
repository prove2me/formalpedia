-- Prove2me | solution 1 for section5_large_grid_fits_window
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:09:12.316788+00:00
-- url     : https://prove2.me/submissions/6f1b65ec-e7a3-466a-9f78-fcd2bf1a036d

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Mathlib
import Theorems.Thm_section5_window_precision_bounds
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution (n q : ℕ) (hn : 1 ≤ n)
    (hM : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) :
    2*section5_window_precision n+6 ≤ q := by
  have hb := (section5_window_precision_bounds n hn).2.1
  have hpow : (2:ℝ)^(2*section5_window_precision n+6) ≤ (2:ℝ)^q := by
    rw [pow_add,show 2*section5_window_precision n=section5_window_precision n*2 by omega,pow_mul]
    norm_num only [show (2:ℝ)^6=64 from by norm_num]
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2^section5_window_precision n) hb.le 2
    norm_num only [show (2:ℝ)^40=1099511627776 from by norm_num] at hM
    nlinarith
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hpow
