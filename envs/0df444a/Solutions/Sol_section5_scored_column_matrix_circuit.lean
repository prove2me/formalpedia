-- Prove2me | solution 1 for section5_scored_column_matrix_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:26:25.418899+00:00
-- url     : https://prove2.me/submissions/baaad8ed-b575-4d9c-98ec-fc558f2dbb0c

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
import Definitions.Def_Section5Verified_Section5ScoredColumnSelection
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_scored_column_selection_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! The selected payload is an actual maximal column of the original decoded
integer matrix. This connects the score/scan circuit to the direction decoder. -/



theorem section5_record_matrix_column_score {m n R b : ℕ} (p : Fin n → Fin R ↪ Fin m)
    (re im : Fin (n*(b+1)) ↪ Fin R) (z : Qubits m) (j : Fin n) :
    (section5_record_integer_matrix p re im z).columnScore j=
      section5_record_column_square p
        (fun i e => re (finProdFinEquiv (i,e))) (fun i e => im (finProdFinEquiv (i,e))) j z := by
  rfl



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m N R b : ℕ}
    (score : Fin (2*(N+1)+b+b+1) ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m)
    (re im : Fin ((N+1)*(b+1)) ↪ Fin R)
    (anc : Fin (2*(N+1)+b+b+1+1) ↪ Fin m) (t : Fin m)
    (ctrl : Fin N ↪ Fin m) (scanAnc : Fin 1 ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hre : ∀ i f, re i ≠ score f) (him : ∀ i f, im i ≠ score f)
    (hpa : ∀ i e j, p i e ≠ anc j) (hpt : ∀ i e, p i e ≠ t) (hta : ∀ j, t ≠ anc j)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hscan : ∀ i e j, p i e ≠ scanAnc j) (hca : ∀ i j, ctrl i ≠ scanAnc j) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ ((16*(2*(N+1)+b+b+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1)))*(N+1)+
        (16*(2*(N+1)+b+b+1)+1+7*R)*N ∧
      ∀ z : Qubits m,
        z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i (score e))=false) →
        (∀ i, z (ctrl i)=false) → (∀ j, z (scanAnc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∃ winner : Fin (N+1),
            (∀ i, (section5_record_integer_matrix p re im z).columnScore i ≤
              (section5_record_integer_matrix p re im z).columnScore winner) ∧
            (∀ i, section5_integer_vector_read (re.trans (p 0)) z' i=
              (section5_record_integer_matrix p re im z).re i winner) ∧
            (∀ i, section5_integer_vector_read (im.trans (p 0)) z' i=
              (section5_record_integer_matrix p re im z).im i winner)) ∧
          ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by
  obtain ⟨c,hc,hact⟩ := section5_scored_column_selection_circuit score p
    (fun i e => re (finProdFinEquiv (i,e))) (fun i e => im (finProdFinEquiv (i,e)))
    anc t ctrl scanAnc hpair (fun i e f => hre _ f) (fun i e f => him _ f)
    hpa hpt hta hctrl hscan hca
  refine ⟨c,hc,?_⟩
  intro z hzt hza hzscore hzc hzs
  obtain ⟨z',hz',⟨winner,hpayload,hmax⟩,hoff⟩ := hact z hzt hza hzscore hzc hzs
  refine ⟨z',hz',⟨winner,?_,?_,?_⟩,hoff⟩
  · intro i
    simpa only [section5_record_matrix_column_score] using hmax i
  · intro i
    change section5_integer_bit_value (section5_twos_coefficient (b+1))
      (fun e => z' (p 0 (re (finProdFinEquiv (i,e)))))=
        section5_integer_bit_value (section5_twos_coefficient (b+1))
          (fun e => z (p winner (re (finProdFinEquiv (i,e)))))
    congr 1
    funext e
    apply hpayload
    rintro ⟨f,hf⟩
    exact hre _ f hf.symm
  · intro i
    change section5_integer_bit_value (section5_twos_coefficient (b+1))
      (fun e => z' (p 0 (im (finProdFinEquiv (i,e)))))=
        section5_integer_bit_value (section5_twos_coefficient (b+1))
          (fun e => z (p winner (im (finProdFinEquiv (i,e)))))
    congr 1
    funext e
    apply hpayload
    rintro ⟨f,hf⟩
    exact him _ f hf.symm
