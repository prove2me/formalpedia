-- Prove2me | solution 1 for section5_powered_matrix_decoder_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:35:38.884226+00:00
-- url     : https://prove2.me/submissions/d342a6f7-48c5-4afe-ad2c-7c60e4f612fd

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PoweredMatrixDecoder
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
import Mathlib
import Theorems.Thm_section5_column_direction_circuit
import Theorems.Thm_section5_scored_column_matrix_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/































































theorem section5_boolean_circuit_append {m : ℕ} (c d : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (c++d)) ψ=act d.unitary (act c.unitary ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_append,List.reverse_append,List.prod_append]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z









end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
theorem solution {m N R b q k f : ℕ}
    (score : Fin (2*(N+1)+b+b+1) ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m) (re im : Fin ((N+1)*(b+1)) ↪ Fin R)
    (anc : Fin (2*(N+1)+b+b+1+1) ↪ Fin m) (t : Fin m)
    (ctrl : Fin N ↪ Fin m) (scanAnc : Fin 1 ↪ Fin m)
    (np : Fin ((N+1)+b+b+1+1) ↪ Fin m)
    (na : Fin ((N+1)+b+b+1+1+1) ↪ Fin m) (nt : Fin m)
    (dst : Fin (N+1) → Fin (f+2) ↪ Fin m)
    (hf : f ≤ (q+1)*(k+1)) (hfit : (q+1)*(k+1)+2 ≤ b+1)
    (hpair : ∀ i j, i ≠ j → ∀ e g, p i e ≠ p j g)
    (hre : ∀ i e, re i ≠ score e) (him : ∀ i e, im i ≠ score e)
    (hri : ∀ i j, re i ≠ im j)
    (hpa : ∀ i e j, p i e ≠ anc j) (hpt : ∀ i e, p i e ≠ t) (hta : ∀ j, t ≠ anc j)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hscan : ∀ i e j, p i e ≠ scanAnc j) (hca : ∀ i j, ctrl i ≠ scanAnc j)
    (hnpa : ∀ i j, np i ≠ na j) (hntp : nt ∉ Set.range np) (hnta : ∀ j, nt ≠ na j)
    (hdst : ∀ i j, i ≠ j → ∀ e g, dst i e ≠ dst j g)
    (hndst : ∀ i j e, np j ≠ dst i e)
    (hnpf : ∀ e, section5_outside_column_records p ctrl (np e))
    (hnaf : ∀ e, section5_outside_column_records p ctrl (na e))
    (hntf : section5_outside_column_records p ctrl nt)
    (hdf : ∀ i e, section5_outside_column_records p ctrl (dst i e)) :
    ∃ c : Circuit gatesRev m,
      c.size ≤
        (((16*(2*(N+1)+b+b+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1)))*(N+1)+
          (16*(2*(N+1)+b+b+1)+1+7*R)*N)+
        ((16*((N+1)+b+b+1+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1))+
          7*((N+1)*(b+1))+2*(f+2)*(N+1)) ∧
      ∀ z : Qubits m,
        z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i (score e))=false) →
        (∀ i, z (ctrl i)=false) → (∀ j, z (scanAnc j)=false) →
        z nt=false → (∀ j, z (na j)=false) → (∀ e, z (np e)=false) →
        (∀ i e, z (dst i e)=false) →
      ∀ (M : Section5IntegerMatrix (N+1)), IsSelfAdjoint (M.dyadicOperator q) →
        section5_record_integer_matrix p re im z=M.power (k+1) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(k+1) →
        144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f →
      ∀ w : EuclideanSpace ℝ (Fin (N+1)), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          let v : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by
  let A := re.trans (p 0)
  let B := im.trans (p 0)
  have hAB : ∀ i j, A i ≠ B j := by
    intro i j h
    exact hri i j ((p 0).injective h)
  have hAt : ∀ i, A i ≠ nt := by
    intro i h
    exact hntf.1 0 ⟨re i,h⟩
  have hBt : ∀ i, B i ≠ nt := by
    intro i h
    exact hntf.1 0 ⟨im i,h⟩
  have hAp : ∀ i, A i ∉ Set.range np := by
    intro i ⟨e,he⟩
    exact (hnpf e).1 0 ⟨re i,he.symm⟩
  have hBp : ∀ i, B i ∉ Set.range np := by
    intro i ⟨e,he⟩
    exact (hnpf e).1 0 ⟨im i,he.symm⟩
  have hAd : ∀ i j e, A j ≠ dst i e := by
    intro i j e h
    exact (hdf i e).1 0 ⟨re j,h⟩
  have hBd : ∀ i j e, B j ≠ dst i e := by
    intro i j e h
    exact (hdf i e).1 0 ⟨im j,h⟩
  obtain ⟨cs,hs,hsa⟩ := section5_scored_column_matrix_circuit score p re im anc t ctrl scanAnc
    hpair hre him hpa hpt hta hctrl hscan hca
  obtain ⟨cd,hd,hda⟩ := section5_column_direction_circuit (by omega : 1 ≤ N+1) A B np na nt dst
    hf hfit hAB hnpa hntp hnta hAt hBt hAp hBp hdst hAd hBd hndst
  refine ⟨cs++cd,?_,?_⟩
  · simpa only [Circuit.size,List.length_append] using add_le_add hs hd
  · intro z hzt hza hzscore hzc hzs hznt hzna hznp hzd M hM hmatrix
      ε hε hε' hiter hbits w hw herror
    obtain ⟨z1,hz1,⟨j,hmax,hre1,him1⟩,hoff⟩ := hsa z hzt hza hzscore hzc hzs
    have hfresh (v : Fin m) (hv : section5_outside_column_records p ctrl v) : z1 v=z v :=
      hoff v hv.1 hv.2
    have hz1nt : z1 nt=false := (hfresh nt hntf).trans hznt
    have hz1na : ∀ j, z1 (na j)=false := fun j => (hfresh _ (hnaf j)).trans (hzna j)
    have hz1np : ∀ e, z1 (np e)=false := fun e => (hfresh _ (hnpf e)).trans (hznp e)
    have hz1d : ∀ i e, z1 (dst i e)=false := fun i e => (hfresh _ (hdf i e)).trans (hzd i e)
    rw [hmatrix] at hmax hre1 him1
    obtain ⟨z2,hz2,hoff2,hout⟩ := hda z1 hz1nt hz1na hz1np hz1d
      M hM ε hε hε' hiter hbits j hmax hre1 him1 w hw herror
    refine ⟨z2,?_,hout⟩
    rw [section5_boolean_circuit_append,hz1,hz2]
