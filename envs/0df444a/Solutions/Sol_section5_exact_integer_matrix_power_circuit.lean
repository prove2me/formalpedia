-- Prove2me | solution 1 for section5_exact_integer_matrix_power_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:30:33.420655+00:00
-- url     : https://prove2.me/submissions/cbbc9fc5-6e5d-40ff-a7ea-3c33dad9af4a

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
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_fixed_width_matrix_power_circuit
import Theorems.Thm_section5_integer_matrix_bit_bound
import Theorems.Thm_section5_integer_matrix_residue_power
import Theorems.Thm_section5_twos_complement_decode_mod
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! The bounded-window integer decoder is exactly the standard signed binary
linear form. This connects the window analysis to the signed dot-product circuit. -/



theorem section5_twos_complement_value (b : ℕ) (z : Qubits (b+1)) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=
      (bitsToNatLSB z : ℤ)-(if z (Fin.last b) then (2:ℤ)^(b+1) else 0) := by
  unfold section5_integer_bit_value section5_twos_coefficient bitsToNatLSB
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.add_left_inj,↓reduceIte]
  push_cast
  have hi (i : Fin b) : i.val ≠ b := by omega
  simp_rw [if_neg (hi _)]
  cases hz : z (Fin.last b) <;> simp [hz,pow_succ] <;> ring











end
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! Modular complex matrix powers. Working modulo a fixed output width avoids
an increase in register width at each multiplication. Signed decoding agrees with
the same residues; only the final integer output needs an overflow bound. -/

















theorem section5_signed_binary_residue (b : ℕ) (z : Qubits (b+1)) :
    (section5_integer_bit_value (section5_twos_coefficient (b+1)) z:ZMod (2^(b+1)))=
      (bitsToNatLSB z:ZMod (2^(b+1))) := by
  rw [section5_twos_complement_value]
  have hp : (((2:ℤ)^(b+1):ℤ):ZMod (2^(b+1)))=0 := by
    simpa only [Int.cast_pow,Int.cast_ofNat,Nat.cast_pow,Nat.cast_ofNat] using
      (ZMod.natCast_self (2^(b+1)))
  cases z (Fin.last b) <;> simp [hp]











end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Final signed decoding of the fixed-width matrix-power circuit. The register
width is linear in the number of products and the input/dimension bit bounds. -/

@[ext] theorem Section5IntegerMatrix.ext {n : ℕ} {A B : Section5IntegerMatrix n}
    (hre : A.re=B.re) (him : A.im=B.im) : A=B := by
  cases A
  cases B
  cases hre
  cases him
  rfl



theorem section5_signed_matrix_read_residue {m n b : ℕ}
    (p : Fin (2*n*n) → Fin (b+1) ↪ Fin m) (z : Qubits m) :
    (section5_signed_matrix_read p z).residue (b+1)=section5_mod_matrix_read p z := by
  apply Section5ModMatrix.ext <;> funext i j <;>
    exact section5_signed_binary_residue b _

theorem section5_matrix_decode_unique {m n b : ℕ}
    (p : Fin (2*n*n) → Fin (b+1) ↪ Fin m) (z : Qubits m) (A : Section5IntegerMatrix n)
    (hmod : section5_mod_matrix_read p z=A.residue (b+1))
    (hbound : A.Bounded ((2:ℤ)^b-1)) : section5_signed_matrix_read p z=A := by
  apply Section5IntegerMatrix.ext <;> funext i j
  · have hm := congrArg (fun M : Section5ModMatrix n (b+1) => M.re i j) hmod
    have hb := abs_le.mp (hbound.1 i j)
    exact section5_twos_complement_decode_mod b _ _ hm (by omega) (by omega)
  · have hm := congrArg (fun M : Section5ModMatrix n (b+1) => M.im i j) hmod
    have hb := abs_le.mp (hbound.2 i j)
    exact section5_twos_complement_decode_mod b _ _ hm (by omega) (by omega)



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m n b K a c : ℕ}
    (hn : n ≤ 2^c) (hwidth : (K+1)*(a+c+1) < b)
    (p : Fin (K+1) → Fin (2*n*n) → Fin (b+1) ↪ Fin m)
    (anc : Fin (b+1+1) ↪ Fin m) (t : Fin m)
    (hcomponents : ∀ s i j, i ≠ j → ∀ e f, p s i e ≠ p s j f)
    (hstages : ∀ s v, s ≠ v → ∀ i j e f, p s i e ≠ p v j f)
    (hpa : ∀ s i e j, p s i e ≠ anc j) (hpt : ∀ s i e, p s i e ≠ t)
    (hta : ∀ j, t ≠ anc j) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (88*n^3*(b+1)^3)*K ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ s : Fin (K+1), 0 < s.val → ∀ i e, z (p s i e)=false) →
        (section5_signed_matrix_read (p 0) z).Bounded ((2:ℤ)^a) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          section5_signed_matrix_read (p (Fin.last K)) z'=
            (section5_signed_matrix_read (p 0) z).power (K+1) ∧
          z' t=false ∧ (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ s : Fin K, ∀ i, j ∉ Set.range (p s.succ i)) → z' j=z j := by
  obtain ⟨circ,hsize,hact⟩ := section5_fixed_width_matrix_power_circuit p anc t
    hcomponents hstages hpa hpt hta
  refine ⟨circ,hsize,?_⟩
  intro z hzt hza hz0 hA
  obtain ⟨z',hz',hmod,hzt',hza',hoff⟩ := hact z hzt hza hz0
  let A := section5_signed_matrix_read (p 0) z
  have hres : section5_mod_matrix_read (p (Fin.last K)) z'=(A.power (K+1)).residue (b+1) := by
    rw [hmod,← section5_signed_matrix_read_residue,← section5_integer_matrix_residue_power]
  have hB := section5_integer_matrix_bit_bound A a c hn hA (K+1)
  have hpow : (2:ℤ)^((K+1)*(a+c+1)) < (2:ℤ)^b :=
    pow_lt_pow_right₀ (by norm_num) hwidth
  have hbound : (A.power (K+1)).Bounded ((2:ℤ)^b-1) := by
    exact ⟨fun i j => by have := hB.1 i j; omega,fun i j => by have := hB.2 i j; omega⟩
  exact ⟨z',hz',section5_matrix_decode_unique _ _ _ hres hbound,hzt',hza',hoff⟩
