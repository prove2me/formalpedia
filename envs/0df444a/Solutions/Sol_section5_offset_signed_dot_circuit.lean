-- Prove2me | solution 1 for section5_offset_signed_dot_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:15:42.05185+00:00
-- url     : https://prove2.me/submissions/3e4d2aca-a142-4e7d-bb4a-7442aca8ee34

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OffsetDotCircuit
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Definitions.Def_Section5Verified_Section5WeightedAccumulator
import Mathlib
import Theorems.Thm_section5_signed_integer_dot_circuit
import Theorems.Thm_section5_weighted_accumulator_circuit
import Theorems.Thm_section5_weighted_accumulator_value
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Signed binary dot products are compiled by reducing each signed coefficient modulo
the accumulator modulus. Negative coefficients require no additional circuit gates. -/



theorem section5_residue_coefficient_cast (w : ℕ) (v : ℤ) :
    (section5_residue_coefficient w v : ZMod (2^w))=(v : ZMod (2^w)) := by
  have hnonneg : 0 ≤ v%((2^w:ℕ):ℤ) := Int.emod_nonneg _ (by positivity)
  have hh := congrArg (fun x : ℤ => (x : ZMod (2^w))) (Int.toNat_of_nonneg hnonneg)
  simpa only [section5_residue_coefficient,Int.cast_natCast,ZMod.intCast_mod] using hh













end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Offset-binary fixed-point estimates need no physical recoding: accumulate their
ordinary binary value, then subtract the fixed midpoint times the second vector. -/



theorem section5_unsigned_bit_value {a : ℕ} (z : Qubits a) :
    section5_integer_bit_value (section5_unsigned_coefficient a) z=(bitsToNatLSB z : ℤ) := by
  unfold section5_integer_bit_value section5_unsigned_coefficient bitsToNatLSB
  push_cast
  rfl



theorem section5_offset_bias_length {m n b : ℕ} (w a : ℕ)
    (x : Fin n → Fin (b+1) → Fin m) :
    (section5_offset_bias_terms w a x).length=n*(b+1) := by
  simp [section5_offset_bias_terms]

theorem section5_offset_bias_sum {m n b : ℕ} (w a : ℕ)
    (x : Fin n → Fin (b+1) → Fin m) (z : Qubits m) :
    (section5_binary_weighted_sum (section5_offset_bias_terms w a x) z : ZMod (2^w))=
      ((∑ i : Fin n, -(2:ℤ)^a*
        section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ x i) : ℤ) : ZMod (2^w)) := by
  simp only [section5_binary_weighted_sum,section5_offset_bias_terms,List.map_map,
    Finset.sum_map_toList,Function.comp_apply,Fintype.sum_prod_type,section5_integer_bit_value]
  simp_rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : z (x i j)
  · simp only [Function.comp_apply,hz,↓reduceIte]
    simpa only [Int.cast_mul,Int.cast_neg,Int.cast_pow,Int.cast_ofNat] using
      section5_residue_coefficient_cast w (-(2:ℤ)^a*section5_twos_coefficient (b+1) j)
  · simp only [Function.comp_apply,hz,Bool.false_eq_true,↓reduceIte,Nat.cast_zero,
      Int.cast_zero,mul_zero]









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
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! A clean reversible accumulator for an arbitrary binary weighted sum. The gate count
is linear in the accumulator width and the number of summands. -/





theorem section5_weighted_step_off {m w : ℕ} (p : Fin w ↪ Fin m)
    (a : Fin m × ℕ) (z : Qubits m) (j : Fin m) (hj : j ∉ Set.range p) :
    section5_weighted_step p a z j=z j := by
  unfold section5_weighted_step
  split_ifs
  · exact updateOn_apply_not_mem p z _ hj
  · rfl

theorem section5_weighted_eval_off {m w : ℕ} (p : Fin w ↪ Fin m)
    (ops : List (Fin m × ℕ)) (z : Qubits m) (j : Fin m) (hj : j ∉ Set.range p) :
    section5_weighted_eval p ops z j=z j := by
  induction ops generalizing z with
  | nil => rfl
  | cons a ops ih =>
    exact (ih (section5_weighted_step p a z)).trans (section5_weighted_step_off p a z j hj)









end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution {m n a b w : ℕ}
    (u : Fin n → Fin (a+1) → Fin m) (x : Fin n → Fin (b+1) → Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p)
    (hxa : ∀ i j k, x i j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (16*w+6)*(n*(a+2)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (bitsToNatLSB (z' ∘ p) : ZMod (2^w))=
            (bitsToNatLSB (z ∘ p) : ZMod (2^w))+
              ((∑ i : Fin n, ((bitsToNatLSB (z ∘ u i):ℤ)-(2:ℤ)^a)*
                section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ x i) : ℤ) :
                  ZMod (2^w)) := by
  classical
  obtain ⟨c,hc,hcact⟩ := section5_signed_integer_dot_circuit
    (section5_unsigned_coefficient (a+1)) (section5_twos_coefficient (b+1)) u x
    p anc hpa t htp hta hut hxt hup hxp
  have hctrl : ∀ v ∈ section5_offset_bias_terms w a x,
      (∀ i, v.1 ≠ p i) ∧ (∀ k, v.1 ≠ anc k) := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    exact ⟨fun i heq => hxp _ _ ⟨i,heq.symm⟩,hxa _ _⟩
  obtain ⟨d,hd,hdact⟩ := section5_weighted_accumulator_circuit p anc hpa
    (section5_offset_bias_terms w a x) hctrl
  refine ⟨c++d,?_,?_⟩
  · rw [section5_offset_bias_length] at hd
    simp only [Circuit.size,List.length_append] at *
    nlinarith
  · intro z hzt hzanc
    obtain ⟨z1,hz1,hoff1,hval1⟩ := hcact z hzt hzanc
    have hclean : ∀ j, z1 (anc j)=false := by
      intro j
      rw [hoff1 (anc j) (by rintro ⟨i,hi⟩; exact hpa i j hi),hzanc j]
    refine ⟨section5_weighted_eval p (section5_offset_bias_terms w a x) z1,?_,?_,?_⟩
    · rw [section5_boolean_circuit_append,hz1,hdact z1 hclean]
    · intro j hj
      exact (section5_weighted_eval_off p _ z1 j hj).trans (hoff1 j hj)
    · rw [section5_weighted_accumulator_value p _ (fun v hv => (hctrl v hv).1) z1,
        ZMod.natCast_mod,Nat.cast_add,hval1,section5_offset_bias_sum]
      have hread (i : Fin n) : z1 ∘ x i=z ∘ x i := by
        funext j
        exact hoff1 (x i j) (hxp i j)
      simp_rw [hread,section5_unsigned_bit_value]
      push_cast
      rw [add_assoc,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
