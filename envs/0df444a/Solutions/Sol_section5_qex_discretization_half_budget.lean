-- Prove2me | solution 1 for section5_qex_discretization_half_budget
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:49:11.232625+00:00
-- url     : https://prove2.me/submissions/536d5d12-747e-4c99-8d4a-d41669c72322

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Mathlib
import Theorems.Thm_section5_hermite_discretization_budget
import Theorems.Thm_section5_lemma_5_1
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement
theorem solution (n q D : ℕ) (hq : 0 < q) (hD : 1 ≤ D)
    (η : ℝ) (hη : 0 < η) (hsize : 64*(n:ℝ)^2*(D+1) ≤ (2:ℝ)^q)
    (h1 : 20736*(n:ℝ)^2*(D+1)/η^2 ≤ (2:ℝ)^q)
    (h2 : 165888*(n:ℝ)/η^4 ≤ (2:ℝ)^q)
    (h3 : 4/Real.pi*Real.log (12*Real.sqrt (2*n)/η) ≤ (2:ℝ)^q)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖inner ℂ (section5_flat_hermite_tensor n q D a) (section5_qex_phase_input w q)-
        (hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤ η/2 := by
  exact (section5_lemma_5_1 n q D hq hD hsize w hw).trans
    (section5_hermite_discretization_budget n D ((2:ℝ)^q) η
      (by positivity) (by positivity) (by positivity) hη h1 h2 h3)
