-- Prove2me | solution 1 for section5_uniform_matrix_power_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:36:06.636487+00:00
-- url     : https://prove2.me/submissions/17138cbf-be4c-4b1b-a8d5-b42b9de4feea

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
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
import Theorems.Thm_section5_decoder_parameters_sufficient
import Theorems.Thm_section5_decoder_power_gate_bound
import Theorems.Thm_section5_dyadic_entry_bound
import Theorems.Thm_section5_exact_integer_matrix_power_circuit
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Statistical operator error implies the real, sign-ambiguous direction guarantee
used by Theorem 5.6. This is the reconstruction guarantee; no efficient measurement
or classical eigenvector algorithm is assumed to have been constructed here. -/

theorem section5_complexify_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖section5_complexify w‖=‖w‖ := by
  have hs : ‖section5_complexify w‖^2=‖w‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,section5_complexify,WithLp.ofLp_toLp,
      Complex.norm_real]
  nlinarith [norm_nonneg w,norm_nonneg (section5_complexify w)]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
theorem solution {m n : ℕ} (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (p : Fin (section5_decoder_iterations n ε+1) → Fin (2*n*n) →
      Fin (section5_decoder_integer_width n ε+1) ↪ Fin m)
    (anc : Fin (section5_decoder_integer_width n ε+1+1) ↪ Fin m) (t : Fin m)
    (hcomponents : ∀ s i j, i ≠ j → ∀ e f, p s i e ≠ p s j f)
    (hstages : ∀ s v, s ≠ v → ∀ i j e f, p s i e ≠ p v j f)
    (hpa : ∀ s i e j, p s i e ≠ anc j) (hpt : ∀ s i e, p s i e ≠ t)
    (hta : ∀ j, t ≠ anc j) :
    ∃ circ : Circuit gatesRev m, (circ.size:ℝ) ≤ (10:ℝ)^25*((n:ℝ)/ε)^13 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ s : Fin (section5_decoder_iterations n ε+1), 0 < s.val → ∀ i e, z (p s i e)=false) →
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
        ‖(section5_signed_matrix_read (p 0) z).dyadicOperator (section5_decoder_fraction_bits n ε)-
          rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ 1 →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          section5_signed_matrix_read (p (Fin.last (section5_decoder_iterations n ε))) z'=
            (section5_signed_matrix_read (p 0) z).power (section5_decoder_iterations n ε+1) ∧
          z' t=false ∧ (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ s : Fin (section5_decoder_iterations n ε), ∀ i,
            j ∉ Set.range (p s.succ i)) → z' j=z j := by
  obtain ⟨hiter,hbits,hnc,hfit,hout,hwidth⟩ := section5_decoder_parameters_sufficient n ε hε
  obtain ⟨circ,hsize,hact⟩ := section5_exact_integer_matrix_power_circuit
    (a:=section5_decoder_fraction_bits n ε+1) (c:=section5_binary_precision n)
    hnc hwidth p anc t hcomponents hstages hpa hpt hta
  refine ⟨circ,?_,?_⟩
  · have hh : (circ.size:ℝ) ≤
        ((88*n^3*(section5_decoder_integer_width n ε+1)^3)*section5_decoder_iterations n ε:ℕ) := by
      exact_mod_cast hsize
    exact hh.trans (section5_decoder_power_gate_bound n hn ε hε hε')
  · intro z hzt hza hz0 w hw herror
    have hbound := section5_dyadic_entry_bound (section5_signed_matrix_read (p 0) z)
      (section5_decoder_fraction_bits n ε) (section5_complexify w)
      (by rwa [section5_complexify_norm]) herror
    exact hact z hzt hza hz0 hbound
