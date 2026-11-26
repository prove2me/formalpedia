-- Prove2me | solution 1 for section5_column_direction_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:30:06.897775+00:00
-- url     : https://prove2.me/submissions/668d5bd1-3e98-46a9-82ce-439d675dc06d

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
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_decoder_output_circuit
import Theorems.Thm_section5_real_candidate_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact integer-matrix semantics of the larger-part selection circuit.
Equality of squared norms retains the real part, as in realCandidateAt. -/





@[simp] theorem section5_integer_vector_coordinate_apply (n b : ℕ) (i : Fin n) (e : Fin (b+1)) :
    section5_integer_vector_coordinate n b i e=finProdFinEquiv (i,e) := rfl



end
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
theorem solution {m n b q k f : ℕ} (hn : 1 ≤ n)
    (A B : Fin (n*(b+1)) ↪ Fin m)
    (p : Fin (n+b+b+1+1) ↪ Fin m) (anc : Fin (n+b+b+1+1+1) ↪ Fin m) (t : Fin m)
    (dst : Fin n → Fin (f+2) ↪ Fin m)
    (hf : f ≤ (q+1)*(k+1)) (hfit : (q+1)*(k+1)+2 ≤ b+1)
    (hAB : ∀ i j, A i ≠ B j)
    (hpa : ∀ i j, p i ≠ anc j) (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hAt : ∀ i, A i ≠ t) (hBt : ∀ i, B i ≠ t)
    (hAp : ∀ i, A i ∉ Set.range p) (hBp : ∀ i, B i ∉ Set.range p)
    (hpair : ∀ i j, i ≠ j → ∀ e c, dst i e ≠ dst j c)
    (hAd : ∀ i j e, A j ≠ dst i e) (hBd : ∀ i j e, B j ≠ dst i e)
    (hpd : ∀ i j e, p j ≠ dst i e) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ (16*(n+b+b+1+1)+6)*((n+n)*(b+1)*(b+1))+7*(n*(b+1))+2*(f+2)*n ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ e, z (p e)=false) → (∀ i e, z (dst i e)=false) →
      ∀ (M : Section5IntegerMatrix n), IsSelfAdjoint (M.dyadicOperator q) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1) →
        144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f →
      ∀ j : Fin n, (∀ i, (M.power (k+1)).columnScore i ≤ (M.power (k+1)).columnScore j) →
        (∀ i, section5_integer_vector_read A z i=(M.power (k+1)).re i j) →
        (∀ i, section5_integer_vector_read B z i=(M.power (k+1)).im i j) →
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ v, v ∉ Set.range A → v ∉ Set.range B → v ∉ Set.range p →
            (∀ i, v ∉ Set.range (dst i)) → z' v=z v) ∧
          let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by
  obtain ⟨cs,hs,hsa⟩ := section5_real_candidate_circuit A B p anc t hAB hpa htp hta hAt hBt hAp hBp
  obtain ⟨co,ho,hoa⟩ := section5_dyadic_decoder_output_circuit hn A
    (section5_integer_vector_coordinate n b) dst hf hfit hpair hAd
  refine ⟨cs++co,?_,?_⟩
  · simpa only [Circuit.size,List.length_append] using add_le_add hs ho
  · intro z hzt hza hzp hzd M hM ε hε hε' hiter hbits j hmax hre him w hw herror
    obtain ⟨z1,hz1,hcand,hoff1⟩ := hsa z hzt hza hzp
    have hz1d : ∀ i e, z1 (dst i e)=false := by
      intro i e
      apply Eq.trans (hoff1 _ ?_ ?_ ?_) (hzd i e)
      · rintro ⟨a,ha⟩
        exact hAd i a e ha
      · rintro ⟨a,ha⟩
        exact hBd i a e ha
      · rintro ⟨a,ha⟩
        exact hpd i a e ha
    have hread : ∀ i, section5_integer_bit_value (section5_twos_coefficient (b+1))
        (z1 ∘ A ∘ section5_integer_vector_coordinate n b i)=(M.power (k+1)).realCandidateAt j i := by
      intro i
      simpa only [section5_integer_vector_read,section5_integer_vector_coordinate_apply,Function.comp_def]
        using hcand (M.power (k+1)) j hre him i
    obtain ⟨z2,hz2,hoff2,hout⟩ := hoa z1 hz1d M hM ε hε hε' hiter hbits j hmax hread w hw herror
    refine ⟨z2,?_,?_,hout⟩
    · rw [section5_boolean_circuit_append,hz1,hz2]
    · intro v hvA hvB hvp hvd
      exact (hoff2 v hvd).trans (hoff1 v hvA hvB hvp)
