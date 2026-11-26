-- Prove2me | solution 1 for section5_grid_exp_sum
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:17.795379+00:00
-- url     : https://prove2.me/submissions/bedb6f36-7a60-418c-ab4f-d01de890baa7

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
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite

/-! Matching the exact physical Hermite grid normalization and bit convention. -/









theorem section5_scalarGrid_grid_node {q : ℕ} (hq : 0 < q) (z : Qubits q) :
    scalarGrid z = -gridRadius (2^q)+(bitsEquivFin q z : ℝ)*gridSpacing (2^q) := by
  rcases q with _ | q
  · omega
  simp only [scalarGrid,gridRadius,gridSpacing,bitsEquivFin_apply,QuantumLTF.Example.bitsValue,
    bitsToNat,Nat.add_sub_cancel,pow_succ,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring













end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite

/-! The sampled phase vector is exactly the phase branch of the public QEX state. -/





theorem section5_gridPoint_flatReg {n q : ℕ} (z : Fin n → Qubits q) :
    gridPoint (flatReg n q z) = WithLp.toLp 2 (fun i => scalarGrid (z i)) := by
  have hflat (i : Fin n) : (fun j : Fin q => flatReg n q z
      ⟨i.val*q+j.val,by nlinarith [Nat.mul_le_mul_right q (Nat.succ_le_iff.mpr i.isLt),j.isLt]⟩) = z i := by
    funext j
    simpa only [flatReg,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using
      congrArg (fun p : Fin n × Fin q => z p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
  simp only [gridPoint,scalarGrid,hflat]









theorem section5_bit_grid_node_eq {n q : ℕ} (hq : 0 < q) (z : Fin n → Qubits q) :
    (WithLp.toLp 2 (section5_grid_node n (2^q) (section5_bit_grid_equiv n q z)) :
      EuclideanSpace ℝ (Fin n)) = gridPoint (flatReg n q z) := by
  rw [section5_gridPoint_flatReg]
  ext i
  exact (section5_scalarGrid_grid_node hq (z i)).symm





end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite
theorem solution {n q : ℕ} (hq : 0 < q) :
    (∑ j : Fin n → Fin (2^q),
      Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n (2^q) j) : EuclideanSpace ℝ (Fin n))‖^2/2)) =
        ∑ z : Qubits (n*q), gridWeight z := by
  let F := fun j : Fin n → Fin (2^q) =>
    Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n (2^q) j) : EuclideanSpace ℝ (Fin n))‖^2/2)
  calc
    _ = ∑ z : Fin n → Qubits q, F (section5_bit_grid_equiv n q z) :=
      ((section5_bit_grid_equiv n q).sum_comp F).symm
    _ = ∑ z : Fin n → Qubits q, gridWeight (flatReg n q z) := by
      apply Finset.sum_congr rfl
      intro z hz
      dsimp only [F]
      rw [section5_bit_grid_node_eq hq]
      rfl
    _ = _ := (section5_register_equiv n q).sum_comp gridWeight
