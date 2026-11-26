-- Prove2me | solution 1 for section5_dyadic_decoder_output_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:21:35.738239+00:00
-- url     : https://prove2.me/submissions/7831cd8f-cb6b-4ce6-a92a-3dac27c0e25b

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
import Definitions.Def_Section5Verified_Section5DyadicVectorOutput
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_integer_reconstruction
import Theorems.Thm_section5_dyadic_vector_output_circuit
import Theorems.Thm_section5_scaled_integer_candidate_bounds
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives ContinuousLinearMap InnerProductSpace
theorem solution {m r n d q k f : ℕ} (hn : 1 ≤ n)
    (data : Fin r ↪ Fin m) (src : Fin n → Fin (d+1) ↪ Fin r)
    (dst : Fin n → Fin (f+2) ↪ Fin m)
    (hf : f ≤ (q+1)*(k+1)) (hfit : (q+1)*(k+1)+2 ≤ d+1)
    (hpair : ∀ i j, i ≠ j → ∀ e b, dst i e ≠ dst j b)
    (hdata : ∀ i j e, data j ≠ dst i e) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(f+2)*n ∧
      ∀ (z : Qubits m), (∀ i e, z (dst i e)=false) →
      ∀ (A : Section5IntegerMatrix n), IsSelfAdjoint (A.dyadicOperator q) →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1) →
        144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f →
      ∀ (j : Fin n), (∀ i, (A.power (k+1)).columnScore i ≤ (A.power (k+1)).columnScore j) →
        (∀ i, section5_integer_bit_value (section5_twos_coefficient (d+1))
          (z ∘ data ∘ src i)=(A.power (k+1)).realCandidateAt j i) →
      ∀ (w : EuclideanSpace ℝ (Fin n)), ‖w‖=1 →
        ‖A.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ v, (∀ i, v ∉ Set.range (dst i)) → z' v=z v) ∧
          let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by
  have hfit' : (q+1)*(k+1)-f+(f+1+1) ≤ d+1 := by omega
  obtain ⟨c,hc,hact⟩ := section5_dyadic_vector_output_circuit data src dst hf hfit' hpair hdata
  refine ⟨c,hc,?_⟩
  intro z hz0 A hA ε hε hε' hiter hbits j hmax hread w hw herror
  have hvec : section5_signed_dyadic_vector src ((q+1)*(k+1)) (z ∘ data)=
      ((2:ℝ)^((q+1)*(k+1)))⁻¹ •
        (WithLp.toLp 2 (fun i => ((A.power (k+1)).realCandidateAt j i:ℝ))) := by
    ext i
    simp only [section5_signed_dyadic_vector,PiLp.smul_apply,WithLp.ofLp_toLp,
      smul_eq_mul]
    exact congrArg (fun v : ℤ => ((2:ℝ)^((q+1)*(k+1)))⁻¹*(v:ℝ)) (hread i)
  have hb := section5_scaled_integer_candidate_bounds hn A q k hA w hw (ε/2000)
    (by positivity) (by linarith) herror j hmax
  have hcoord : ∀ i, |section5_signed_dyadic_vector src ((q+1)*(k+1)) (z ∘ data) i| ≤ 1 := by
    intro i
    have hh := PiLp.norm_apply_le (section5_signed_dyadic_vector src ((q+1)*(k+1)) (z ∘ data)) i
    rw [Real.norm_eq_abs,hvec] at hh
    rw [hvec]
    exact hh.trans hb.2
  obtain ⟨z',hz',hoff,hout⟩ := hact z hz0 hcoord
  refine ⟨z',hz',hoff,?_⟩
  dsimp only
  rw [hout,hvec]
  exact section5_dyadic_integer_reconstruction hn A q k f hA ε hε hε' hiter hbits j hmax w hw herror
